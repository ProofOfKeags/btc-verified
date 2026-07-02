{
  description = "Development shell for btc-verified";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { nixpkgs, ... }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];

      forAllSystems = nixpkgs.lib.genAttrs systems;
    in
    {
      devShells = forAllSystems (system:
        let
          pkgs = import nixpkgs { inherit system; };
        in
        {
          default = pkgs.mkShell {
            packages = with pkgs; [
              cacert
              curl
              git
              stdenv.cc

              # elan is used instead of nixpkgs#lean4 because nixpkgs currently
              # has Lean 4.29.1, while we need leanprover/lean4:v4.30.0-rc2.
              elan
            ];

            shellHook = ''
              # Use Nix's certificate bundle for HTTPS fetches from tools such
              # as curl, git, elan, and Lake.
              export SSL_CERT_FILE="${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt"
              export GIT_SSL_CAINFO="$SSL_CERT_FILE"

              # Print the repository-pinned Lean toolchain and the usual build
              # command when entering the shell from the project root.
              if [ -f lean-toolchain ]; then
                echo "btc-verified dev shell"
                echo "Lean toolchain: $(cat lean-toolchain)"
                echo "Run: lake exe cache get && lake build"
              fi
            '';
          };
        });
    };
}
