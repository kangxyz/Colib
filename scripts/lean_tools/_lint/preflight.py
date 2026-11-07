"""Recognize the pinned adapter before Lean imports its dependency API.

Unknown configurations retain the configured native lint command. Path dependencies
are accepted only with the same exact pinned source bytes, allowing tiny fixtures.
"""
import hashlib
import json
from pathlib import Path
import sys
import tomllib

PIN = "66e469188fe07963e5cf666c7d4433f45b8131c5"
SOURCES = {
    "lakefile.toml": "acadcd8beb13a53a4ac9399e6706c829309d2380f338d13b037886666f978015",
    "scripts/runLinter.lean": "08f57d26bd3226929d221868fae9b0b79c1f8ca0c1ce5583c55da9ffaf210bbf",
    "Batteries/Tactic/Lint.lean": "70cdcc284aaa3b637fecbbdc91316ad0d0c59c4766637f3e8c38d3f686bd30e8",
    "Batteries/Tactic/Lint/Basic.lean": "907aef469ac1dd6e027083bdda94058b473e3081bd8cc4dcba53e6aba4b0582d",
    "Batteries/Tactic/Lint/Frontend.lean": "21d81a42a41c2df100e892caf7ec75e5c737018660714245d195e133eeb9761f",
    "Batteries/Tactic/Lint/Misc.lean": "a3f05a0e780fb15659a1fe922486fe75362e80f974441b1aa80dd8e04ee097b4",
    "Batteries/Tactic/Lint/Simp.lean": "18b9a43f1e452aaa9bb509246f1e3a6cc6f91066810c48ec9e2e3dd6b6a91299",
    "Batteries/Tactic/Lint/TypeClass.lean": "30a23854f7607f887b443101771a6934d5137f581761ed204c8c6e0687a8aa3a"
}


def provider_directory(root=Path.cwd()):
    try:
        # Lake prefers lakefile.lean when both files exist; a TOML selector cannot
        # establish that active configuration's driver or arguments.
        if (root / "lakefile.lean").exists():
            return False
        if (root / ".lake/package-overrides.json").exists():
            return False
        config = tomllib.loads((root / "lakefile.toml").read_text())
        if config.get("packagesDir", ".lake/packages") != ".lake/packages":
            return False
        args = config["lintDriverArgs"]
        if (config.get("lintDriver") != "batteries/runLinter"
                or config.get("builtinLint") is not True or not isinstance(args, list)):
            return False
        if not args or not all(isinstance(a, str) and a and
                (not a.startswith("-") or a in {"--no-build", "--trace", "-v"}) for a in args):
            return False
        if not any(not a.startswith("-") for a in args):
            return False
        if "--no-build" not in args:
            return False
        manifest = json.loads((root / "lake-manifest.json").read_text())
        if manifest.get("packagesDir", ".lake/packages") != ".lake/packages":
            return False
        package, = [p for p in manifest["packages"] if p["name"] == "batteries"]
        if (package.get("configFile", "lakefile.toml") != "lakefile.toml"
                or package.get("manifestFile", "lake-manifest.json") != "lake-manifest.json"
                or package.get("subDir") is not None):
            return False
        if package["type"] == "git":
            if package.get("rev") != PIN:
                return False
            directory = root / manifest.get("packagesDir", ".lake/packages") / "batteries"
        elif package["type"] == "path":
            directory = root / package["dir"]
        else:
            return False
        if (directory / "lakefile.lean").exists():
            return False
        if all(hashlib.sha256((directory / name).read_bytes()).hexdigest() == expected
               for name, expected in SOURCES.items()):
            return directory.resolve()
        return False
    except (OSError, ValueError, KeyError, TypeError):
        return False


def supported(root=Path.cwd()):
    return bool(provider_directory(root))


if __name__ == "__main__":
    directory = provider_directory()
    if directory and sys.argv[1:] == ["--batteries-dir"]:
        print(directory)
    if directory and sys.argv[1:] == ["--driver-args"]:
        config = tomllib.loads(Path("lakefile.toml").read_text())
        print(json.dumps([*config["lintDriverArgs"], "--trace"]))
    sys.exit(0 if directory else 1)
