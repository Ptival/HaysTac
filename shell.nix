{ nixpkgs ? import <nixpkgs> {} }:
nixpkgs.stdenv.mkDerivation {
  name = "HaysTac";
  buildInputs = (with nixpkgs; [
    coq_8_7
  ] ++ (with coqPackages_8_7; [
    #coq-ext-lib
  ]));
  shellHook = ''
    export NIXSHELL="$NIXSHELL\[HaysTac\]"
    export SSL_CERT_FILE="/etc/ssl/certs/ca-bundle.crt"
  '';
}
