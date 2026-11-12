#!/usr/bin/env python3

# Build and copy "nd" to "~/.cargo/bin/".
# (Wrapper for "cargo install --path .".)

import os, sys, shutil, argparse, subprocess
from pathlib import Path

def get_cargo_bin_dir():
    cargo_home = os.environ.get("CARGO_HOME")
    if cargo_home is not None:
        return Path(cargo_home) / "bin"
    return Path.home() / ".cargo" / "bin"

def check_path_warning():
    cargo_bin = get_cargo_bin_dir().resolve()
    path_env = os.environ.get("PATH", "")
    system_paths = [Path(p).resolve() for p in path_env.split(os.pathsep) if p]
    if cargo_bin not in system_paths:
        print("\nNOTE: Your Cargo bin directory is currently not in your PATH:")
        print(f"  -> {cargo_bin}")
        print("You may need to restart your shell or add this path")
        print("to your shell configuration (.bashrc, .zshrc) or system environment.")

def main():
    parser = argparse.ArgumentParser(
        description="Installs 'nd' via 'cargo install'.")
    parser.add_argument("--force", action="store_true",
        help="Forces installation and overwrites existing binaries.")
    args = parser.parse_args()

    if not shutil.which("cargo"):
        sys.exit("Error: 'cargo' was not found in your system PATH.\n"
            "Please install Rust via https://rustup.rs/")

    if not Path("Cargo.toml").is_file():
        sys.exit("Error: No 'Cargo.toml' found in the current directory.")

    cmd = "cargo install --path .".split()
    if args.force:
        cmd.append("--force")

    print(f"Running: {' '.join(cmd)}")
    try:
        result = subprocess.run(cmd)
    except KeyboardInterrupt:
        sys.exit("\nInstallation aborted by user.")
    except subprocess.SubprocessError as e:
        sys.exit(f"System error while running cargo: {e}")

    if result.returncode == 0:
        print(f"\nSuccessfully installed! Target directory: {get_cargo_bin_dir()}")
        check_path_warning()
    else:
        sys.exit(result.returncode)

main()
