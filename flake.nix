{
  description = "Lean development flake. Not intended for end users.";

  # We use channels so we're not affected by GitHub's rate limits
  inputs.nixpkgs.url = "https://channels.nixos.org/nixos-unstable/nixexprs.tar.xz";
  inputs.rust-overlay.url = "github:oxalica/rust-overlay";
  # old nixpkgs used for portable release with older glibc (2.27)
  inputs.nixpkgs-old.url = "https://channels.nixos.org/nixos-19.03/nixexprs.tar.xz";
  inputs.nixpkgs-old.flake = false;
  # old nixpkgs used for portable release with older glibc (2.26)
  inputs.nixpkgs-older.url = "https://channels.nixos.org/nixos-18.03/nixexprs.tar.xz";
  inputs.nixpkgs-older.flake = false;

  outputs = inputs: builtins.foldl' inputs.nixpkgs.lib.attrsets.recursiveUpdate {} (map (system:
    let
      pkgs = import inputs.nixpkgs {
        inherit system;
        overlays = [ inputs.rust-overlay.overlays.default ];
      };
      # An old nixpkgs for creating releases with an old glibc
      pkgsDist-old = import inputs.nixpkgs-older { inherit system; };
      # An old nixpkgs for creating releases with an old glibc
      pkgsDist-old-aarch = import inputs.nixpkgs-old { localSystem.config = "aarch64-unknown-linux-gnu"; };

      llvmPackages = pkgs.llvmPackages_19;
      nightlyRust = pkgs.rust-bin.nightly.latest.complete;

      scip-clang = pkgs.stdenv.mkDerivation rec {
        pname = "scip-clang";
        version = "0.4.0";

        src = pkgs.fetchurl {
          url = "https://github.com/sourcegraph/scip-clang/releases/download/v${version}/scip-clang-x86_64-${
            if pkgs.stdenv.isDarwin then "darwin" else "linux"
          }";
          hash = "sha256-Bv0YxXb5eacmxlFZRkTsSjXbT0cfIWCz9y64n6YAF4Q=";
        };

        dontUnpack = true;

        installPhase = ''
          mkdir -p $out/bin
          cp $src $out/bin/scip-clang
          chmod +x $out/bin/scip-clang
        '';

        meta = with pkgs.lib; {
          description = "SCIP indexer for C/C++/Objective-C";
          homepage = "https://github.com/sourcegraph/scip-clang";
          license = licenses.asl20;
          platforms = platforms.unix;
        };
      };

      devShellWithDist = pkgsDist: pkgs.mkShell.override {
          stdenv = pkgs.overrideCC pkgs.stdenv llvmPackages.clang;
        } ({
          buildInputs = with pkgs; [
            cmake gmp libuv ccache pkg-config m4
            llvmPackages.bintools  # wrapped lld
            llvmPackages.llvm  # llvm-symbolizer for asan/lsan
            llvmPackages.libclang.lib
            llvmPackages.libcxx
            llvmPackages.libcxxClang
            gdb
            tree  # for CI

            # CKB / indexing deps
            scip-clang
            nightlyRust
            mold # alternative linker
            # sccache
            rust-analyzer
            clang-tools
            bear
            jq
          ];
          LIBCLANG_PATH = "${llvmPackages.libclang.lib}/lib";
          RUST_SRC_PATH = "${nightlyRust}/lib/rustlib/src/rust/library";
          # RUSTC_WRAPPER = "${pkgs.sccache}/bin/sccache";
          # https://github.com/NixOS/nixpkgs/issues/60919
          hardeningDisable = [ "all" ];
          # more convenient `ctest` output
          CTEST_OUTPUT_ON_FAILURE = 1;
          shellHook = ''
            export LEAN_RUST_THREADS="''${LEAN_RUST_THREADS:-$(nproc)}"
            export RUSTFLAGS="''${RUSTFLAGS:+$RUSTFLAGS }-Z threads=$LEAN_RUST_THREADS"
          '';
        } // pkgs.lib.optionalAttrs pkgs.stdenv.isLinux {
          GMP = (pkgsDist.gmp.override { withStatic = true; }).overrideAttrs (_attrs:
            pkgs.lib.optionalAttrs (pkgs.stdenv.system == "aarch64-linux") {
              # would need additional linking setup on Linux aarch64, we don't use it anywhere else either
              hardeningDisable = [ "stackprotector" ];
            });
          LIBUV = pkgsDist.libuv.overrideAttrs (_attrs: {
            configureFlags = ["--enable-static"];
            hardeningDisable = [ "stackprotector" ];
            # Sync version with CMakeLists.txt
            version = "1.48.0";
            src = pkgs.fetchFromGitHub {
              owner = "libuv";
              repo = "libuv";
              rev = "v1.48.0";
              sha256 = "100nj16fg8922qg4m2hdjh62zv4p32wyrllsvqr659hdhjc03bsk";
            };
            doCheck = false;
          });
          GLIBC = pkgsDist.glibc;
          GLIBC_DEV = pkgsDist.glibc.dev;
          GCC_LIB = pkgsDist.gcc.cc.lib;
          ZLIB = pkgsDist.zlib;
          # for CI coredumps
          GDB = pkgsDist.gdb;
        });
    in {
      devShells.${system} = {
        # The default development shell for working on lean itself
        default = devShellWithDist pkgs;
        oldGlibc = devShellWithDist pkgsDist-old;
        oldGlibcAArch = devShellWithDist pkgsDist-old-aarch;
      };
    }) ["x86_64-linux" "aarch64-linux" "aarch64-darwin"]);
}
