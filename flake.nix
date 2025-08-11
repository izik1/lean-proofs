# This file is pretty general, and you can adapt it in your project replacing
# only `name` and `description` below.

{
  description = "ribit";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, utils, ... }:
    utils.lib.eachDefaultSystem
      (system:
        let
          pkgs = import nixpkgs {
            inherit system;
          };
        in
        rec {
          # `nix develop`
          devShell = pkgs.mkShell
            {
              buildInputs = with pkgs;
                # Tools you need for development go here.
                [
                  elan
                  nixpkgs-fmt
                ];
            };
        }
      );
}
