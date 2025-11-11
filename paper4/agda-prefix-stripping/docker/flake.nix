{
  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in
      {
        formatter = pkgs.nixfmt-rfc-style;
        packages = rec {
          agda = pkgs.agda.withPackages (p: [ p.standard-library ]);
          default = pkgs.buildEnv {
            name = "artifact-tooling";
            paths = with pkgs; [
              agda
              nano
            ];
          };
        };
      }
    );
}
