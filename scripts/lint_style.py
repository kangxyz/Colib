#!/usr/bin/env python3
"""Run Mathlib's unchanged text linters on all Colib and ColibTest source files."""

import os
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
    with tempfile.TemporaryDirectory(prefix="colib-lint-style-") as directory:
        hubs = []
        for package in PACKAGES:
            modules = source_modules(root, package)
            if not modules:
                raise RuntimeError(f"No source modules found for {package}")
            name = f"{package}.ColibStyleLintInputs"
            path = Path(directory, package, "ColibStyleLintInputs.lean")
            if (root / package / path.name).exists():
                raise RuntimeError(f"Reserved lint input module already exists: {name}")
            path.parent.mkdir(parents=True)
            path.write_text("".join(f"import {module}\n" for module in modules))
            hubs.append(name)
            print(f"Text lint: {package}: {len(modules)} source files", flush=True)
        env = dict(os.environ)
        env["LEAN_SRC_PATH"] = directory + os.pathsep + env.get("LEAN_SRC_PATH", "")
        return subprocess.run(
            ["lake", "--no-build", "--log-level=error", "exe", "mathlib/lint-style", *hubs],
            cwd=root, env=env, check=False,
        ).returncode


if __name__ == "__main__":
    raise SystemExit(main())
