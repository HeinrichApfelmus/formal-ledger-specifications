{ nixpkgs ? import <nixpkgs> {} }:
with nixpkgs; let
  agdaDeps = with (import (builtins.fetchTarball
    https://github.com/nixos/nixpkgs/tarball/a7ecde854aee5c4c7cd6177f54a99d2c1ff28a31) ({ # 21.11
      overlays = [ (import (fetchFromGitHub {
        repo = "agda";
        owner = "input-output-hk";
        rev = "d5ea03b96328f38741efef4535197076ff0e05d5";
        sha256 = "WiadZWZvPWcR49JkiXPiMKW3plRjBlR94wyg/aoEoG8=";
      })).overlay ];
    } // (if pkgs.system == "aarch64-darwin" then { system = "x86_64-darwin"; } else {}))); let

    agda-stdlib = agdaPackages.standard-library.overrideAttrs (oldAttrs: {
      version = "1.7";
      src =  fetchFromGitHub {
        repo = "agda-stdlib";
        owner = "input-output-hk";
        rev = "f8fdb925c74e8d3b0c88e2a5520bc11e606d34c6";
        sha256 = "BoK/IZsOn8gnUolI8DOZa6IOoXF8E95s2e8vZyUpMZs=";
      };
    });

    agda-finset = agdaPackages.mkDerivation {
      pname = "agda-finset";
      version = "0.9";
      src = fetchFromGitHub {
        repo = "agda-finset";
        owner = "input-output-hk";
        rev = "939b2578f4f8cb4f02928b30edfc787cabeba171";
        sha256 = "2bUMmUikzNRaEFVkH+Y8ypnNF65d/LNKei6fSJ982AY=";
      };
      meta = {};
      libraryFile = "Finset.agda-lib";
      everythingFile = "src/README.agda";
      buildInputs = [ agda-stdlib ];
    };

    agda-stdlib-meta = agdaPackages.mkDerivation {
      pname = "agda-stdlib-meta";
      version = "0.1";
      src = fetchFromGitHub {
        repo = "stdlib-meta";
        owner = "omelkonian";
        rev = "dadb6a468b9cdc47442b48a47b848f8e8fbffda7";
        sha256 = "YkUtM5Gos6xd7ZsZPqcuVy6DZqNA7n/exPfQngir+y0=";
      };
      patches = [ ./stdlib-meta-update-imports.patch ];
      meta = {};
      libraryFile = "stdlib-meta.agda-lib";
      everythingFile = "Main.agda";
      buildInputs = [ agda-stdlib ];
    };

    deps = [ agda-stdlib agda-finset agda-stdlib-meta ];
  in {
    agda = agda.withPackages { pkgs = deps; ghc = nixpkgs.ghc; };
    ledger = agdaPackages.mkDerivation {
      pname = "Agda-ledger";
      version = "0.1";
      src = ./src;
      meta = {};
      buildInputs = deps;
      everythingFile = "Ledger.lagda";
      postInstall = "cp -r latex $out";
      extraExtensions = [ "hs" "cabal" ];
    };
  };
  agda-ledger = agdaDeps.ledger;
  agdaWithPkgs = agdaDeps.agda;

  ledger-hs-src = stdenv.mkDerivation {
    pname = "Agda-ledger-hs-src";
    version = "0.1";
    src = "${agda-ledger}";
    meta = {};
    buildInputs = [ agdaWithPkgs ];
    buildPhase = "";
    installPhase = ''
      mkdir -p $out
      agda -c --ghc-dont-call-ghc --compile-dir $out HSLedger.agda
      cp HSLedgerTest.hs $out
      cp agda-ledger-executable-spec.cabal $out
      # Append all the modules generated by MAlonzo to the cabal file
      find $out/MAlonzo -name "*.hs" -print | sed "s#^$out/#        #;s#\.hs##;s#/#.#g" >> $out/agda-ledger-executable-spec.cabal
    '';
  };
in {
  agda = agdaWithPkgs;
  agda-ledger = agda-ledger;
  agda-ledger-executable-spec = haskellPackages.callCabal2nix "agda-ledger-executable-spec" "${ledger-hs-src}" {};

  ledger-docs = stdenv.mkDerivation {
    pname = "simple-utxo-ledger-docs";
    version = "0.1";
    src = "${agda-ledger}";
    meta = {};
    buildInputs = [ agdaWithPkgs (texlive.combine {
      inherit (texlive)
        scheme-small
        collection-latexextra
        collection-latexrecommended
        collection-mathscience
        bclogo
        latexmk;
    })];
    buildPhase = ''
      agda --latex Ledger.lagda
      cd latex && latexmk -xelatex Ledger.tex && cd ..
    '';
    installPhase = ''
      mkdir -p $out
      agda --html --html-dir $out/html Ledger.lagda
      cp latex/Ledger.pdf $out
    '';
  };
}
