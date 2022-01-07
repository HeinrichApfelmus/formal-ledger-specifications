{ nixpkgs ? <nixpkgs> }: with (import
      (builtins.fetchTarball https://github.com/nixos/nixpkgs/tarball/7e9b0dff974c89e070da1ad85713ff3c20b0ca97)
      {});
let
  agda-stdlib = agdaPackages.standard-library.overrideAttrs (oldAttrs: {
    version = "1.6";
    src =  fetchFromGitHub {
      repo = "agda-stdlib";
      owner = "input-output-hk";
      rev = "e17a71d045d9a7a4fb9450102ab95b81904b5370";
      sha256 = "08h0n1j6ybqpi4nxm8cli1prsjx44hyfc99b3hlc425h1cvhrbm8";
    };
  });
  agda-finset = agdaPackages.mkDerivation {
    pname = "agda-finset";
    version = "0.9";
    src =  fetchFromGitHub {
      repo = "agda-finset";
      owner = "input-output-hk";
      rev = "94fad4feefc945a76aa088bb10c9aa5964b56132";
      sha256 = "1jm9y5yp21wryv12zd104xn6czvwnzg44d23g8rwgfig46wz1w5x";
    };
    meta = {};
    libraryFile = "Finset.agda-lib";
    everythingFile = "src/README.agda";
    buildInputs = [ agda-stdlib ];
  };
in
agdaPackages.mkDerivation {
  pname = "simple-utxo-ledger";
  version = "0.1";
  src = ./.;
  meta = {};
  buildInputs = [ agda-stdlib agda-finset texlive.combined.scheme-full ];
  everythingFile = "Ledger.lagda";
  installPhase = ''
    mkdir -p $out
    agda --html --html-dir $out/html Ledger.lagda
  	agda --only-scope-checking --latex Ledger.lagda
  	cd latex && xelatex Ledger.tex
  	cp Ledger.pdf $out
  '';
}
