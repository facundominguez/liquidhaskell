{ pkgs ?  import ./nixpkgs.nix {}
, ghc ? pkgs.haskell.compiler.ghc8102
}:

with pkgs;

haskell.lib.buildStackProject ({
  name = "liquidhaskell-stack";
  buildInputs = [ git z3 hostname ];
  ghc = ghc;
  LANG = "en_US.utf8";
  LD_LIBRARY_PATH = ["/home/facundo/tweag/liquidhaskell/smt-switch/build"];
})
