{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes   #-}

module Language.Haskell.Liquid.GHC.Plugin.SpecFinder
    ( findRelevantSpecs
    , findCompanionSpec
    , SpecFinderResult(..)
    , SearchLocation(..)
    , configToRedundantDependencies
    ) where

import           Liquid.GHC.GhcMonadLike as GhcMonadLike ( GhcMonadLike
                                                                          , lookupModSummary
                                                                          , askHscEnv
                                                                          )
import           Language.Haskell.Liquid.GHC.Plugin.Util  ( pluginAbort, deserialiseLiquidLib )
import           Language.Haskell.Liquid.GHC.Plugin.Types
import           Language.Haskell.Liquid.Types.Types
import           Language.Haskell.Liquid.Types.Specs     hiding (Spec)
import qualified Language.Haskell.Liquid.Misc            as Misc
import           Language.Haskell.Liquid.Parse            ( specSpecificationP )
import           Language.Fixpoint.Utils.Files            ( Ext(Spec), withExt )

import           Optics
import qualified Liquid.GHC.API         as O
import           Liquid.GHC.API         as GHC

import           Data.Bifunctor
import           Data.IORef
import           Data.List (find)
import           Data.Maybe

import           Control.Exception
import           Control.Monad.Trans                      ( lift )
import           Control.Monad.Trans.Maybe
import           GHC.Driver.Plugins

import           Text.Megaparsec.Error

type SpecFinder m = GhcMonadLike m => Module -> MaybeT m SpecFinderResult

-- | The result of searching for a spec.
data SpecFinderResult = 
    SpecNotFound Module
  | SpecFound Module SearchLocation BareSpec
  | LibFound  Module SearchLocation LiquidLib

data SearchLocation =
    InterfaceLocation
  -- ^ The spec was loaded from the annotations of an interface.
  | DiskLocation
  -- ^ The spec was loaded from disk (e.g. 'Prelude.spec' or similar)
  deriving Show

-- | Load any relevant spec for the input list of 'Module's, by querying both the 'ExternalPackageState'
-- and the 'HomePackageTable'.
findRelevantSpecs :: ExternalPackageState
                  -> HomePackageTable
                  -> [Module]
                  -- ^ Any relevant module fetched during dependency-discovery.
                  -> TcM [SpecFinderResult]
findRelevantSpecs eps hpt mods = do
    hscEnv <- askHscEnv
    foldlM (loadRelevantSpec (pluginUnit hscEnv)) mempty mods
  where

    loadRelevantSpec :: Unit -> [SpecFinderResult] -> Module -> TcM [SpecFinderResult]
    loadRelevantSpec plUnit !acc currentModule = do
      res <- runMaybeT $ lookupInterfaceAnnotations eps hpt currentModule
      case res of
        Nothing         -> do
          mAssm <- loadModuleAssumptionsIfAny plUnit currentModule
          case mAssm of
            Nothing ->
              return $ SpecNotFound currentModule : acc
            Just specResult ->
              return (specResult : acc)
        Just specResult -> return (specResult : acc)

    loadModuleAssumptionsIfAny plUnit m = do
      let assMod = assumptionsModule plUnit m
      -- loadInterface might mutate the EPS if the module is
      -- not already loaded
      _ <- initIfaceTcRn $ loadInterface "liquidhaskell assumptions" assMod ImportBySystem
      -- read the EPS again
      hscEnv <- askHscEnv
      eps2 <- liftIO $ readIORef (hsc_EPS hscEnv)
      -- now look up the assumptions
      runMaybeT $ lookupInterfaceAnnotations eps2 (hsc_HPT hscEnv) assMod

    pluginUnit =
        moduleUnit
      . fromMaybe (error "liquidhaskell error: can't find plugin module")
      . find isLHPluginModule
      . map (mi_module . lpModule)
      . hsc_plugins
    isLHPluginModule :: Module -> Bool
    isLHPluginModule m = elem (moduleNameString (moduleName m)) ["LiquidHaskell", "LiquidHaskellBoot"]
    assumptionsModule plUnit m =
      mkModule plUnit
        $ mkModuleName
        $ moduleNameString (moduleName m) ++ "_LHAssumptions"

-- | If this module has a \"companion\" '.spec' file sitting next to it, this 'SpecFinder'
-- will try loading it.
findCompanionSpec :: GhcMonadLike m => Module -> m SpecFinderResult
findCompanionSpec m = do
  res <- runMaybeT $ lookupCompanionSpec m
  case res of
    Nothing -> pure $ SpecNotFound m
    Just s  -> pure s

-- | Load a spec by trying to parse the relevant \".spec\" file from the filesystem.
lookupInterfaceAnnotations :: ExternalPackageState -> HomePackageTable -> SpecFinder m
lookupInterfaceAnnotations eps hpt thisModule = do
  lib <- MaybeT $ pure $ deserialiseLiquidLib thisModule eps hpt
  pure $ LibFound thisModule InterfaceLocation lib

-- | If this module has a \"companion\" '.spec' file sitting next to it, this 'SpecFinder'
-- will try loading it.
lookupCompanionSpec :: SpecFinder m
lookupCompanionSpec thisModule = do

  modSummary <- MaybeT $ GhcMonadLike.lookupModSummary (moduleName thisModule)
  file       <- MaybeT $ pure (ml_hs_file . ms_location $ modSummary)
  parsed     <- MaybeT $ do
    mbSpecContent <- liftIO $ try (Misc.sayReadFile (specFile file))
    case mbSpecContent of
      Left (_e :: SomeException) -> pure Nothing
      Right raw -> pure $ Just $ specSpecificationP (specFile file) raw

  case parsed of
    Left peb -> do
      dynFlags <- lift getDynFlags
      let errMsg = O.text "Error when parsing "
             O.<+> O.text (specFile file) O.<+> O.text ":"
             O.<+> O.text (errorBundlePretty peb)
      lift $ pluginAbort (O.showSDoc dynFlags errMsg)
    Right (_, spec) -> do
      let bareSpec = view bareSpecIso spec
      pure $ SpecFound thisModule DiskLocation bareSpec
  where
    specFile :: FilePath -> FilePath
    specFile fp = withExt fp Spec

-- | Returns a list of 'StableModule's which can be filtered out of the dependency list, because they are
-- selectively \"toggled\" on and off by the LiquidHaskell's configuration, which granularity can be
-- /per module/.
configToRedundantDependencies :: forall m. GhcMonadLike m => Config -> m [StableModule]
configToRedundantDependencies cfg = do
  env <- askHscEnv
  catMaybes <$> mapM (lookupModule' env . first ($ cfg)) configSensitiveDependencies
  where
    lookupModule' :: HscEnv -> (Bool, ModuleName) -> m (Maybe StableModule)
    lookupModule' env (fetchModule, modName)
      | fetchModule = liftIO $ lookupLiquidBaseModule env modName
      | otherwise   = pure Nothing

    lookupLiquidBaseModule :: HscEnv -> ModuleName -> IO (Maybe StableModule)
    lookupLiquidBaseModule env mn = do
      res <- liftIO $ findExposedPackageModule env mn (Just "liquidhaskell")
      case res of
        Found _ mdl -> pure $ Just (toStableModule mdl)
        _           -> pure Nothing

-- | Static associative map of the 'ModuleName' that needs to be filtered from the final 'TargetDependencies'
-- due to some particular configuration options.
--
-- Modify this map to add any extra special case. Remember that the semantic is not which module will be
-- /added/, but rather which one will be /removed/ from the final list of dependencies.
--
configSensitiveDependencies :: [(Config -> Bool, ModuleName)]
configSensitiveDependencies = [
    (not . totalityCheck, mkModuleName "Liquid.Prelude.Totality_LHAssumptions")
  , (linear, mkModuleName "Liquid.Prelude.Real_LHAssumptions")
  ]
