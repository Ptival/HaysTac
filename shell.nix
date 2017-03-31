{ nixpkgs ? import <nixpkgs> {} }:
nixpkgs.stdenv.mkDerivation {
  name = "HaysTac";
  buildInputs = (with nixpkgs; [
    coq_8_6
  ] ++ (with coqPackages_8_6; [
    #coq-ext-lib
  ]));
  shellHook = ''
    export SSL_CERT_FILE="/etc/ssl/certs/ca-bundle.crt"
  '';
}
