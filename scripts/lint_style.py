#!/usr/bin/env python3
"""Run Mathlib's unchanged text linters on all Colib and ColibTest source files."""

from contextlib import ExitStack
from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
PACKAGES = ("Colib", "ColibTest")


def source_modules(root: Path, package: str) -> list[str]:
    files = sorted((root / package).rglob("*.lean"))
    if (root / f"{package}.lean").is_file():
        files.insert(0, root / f"{package}.lean")
    return [".".join(p.relative_to(root).with_suffix("").parts) for p in files]


def main(root: Path = ROOT) -> int:
    # The pinned Mathlib CLI checks the direct imports of each supplied module,
    # filtered by those modules' root prefixes. Source-only import hubs include
    # every owned file, including leaf tests; no hub needs compilation.
    with ExitStack() as stack:
        hubs = []
        for package in PACKAGES:
            modules = source_modules(root, package)
            if not modules:
                raise RuntimeError(f"No source modules found for {package}")
            # Lean resolves an existing package directory before the module path.
            # Keep the source-only hub there, and remove it after the native CLI exits.
            directory = Path(stack.enter_context(tempfile.TemporaryDirectory(
                prefix="ColibStyleLintInputs", dir=root / package)))
            name = f"{package}.{directory.name}.Imports"
            path = directory / "Imports.lean"
            path.write_text("".join(f"import {module}\n" for module in modules))
            hubs.append(name)
            print(f"Text lint: {package}: {len(modules)} source files", flush=True)
        return subprocess.run(
            ["lake", "--no-build", "--log-level=error", "exe", "mathlib/lint-style", *hubs],
            cwd=root, check=False,
        ).returncode


if __name__ == "__main__":
    raise SystemExit(main())
