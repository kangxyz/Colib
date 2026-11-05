#!/usr/bin/env python3
"""Build the static encyclopedia from the catalog and a compatible native declaration export."""

import argparse
import json
from pathlib import Path
import shutil
import subprocess

import catalog


def build(declaration_export, output):
    sources, entries = catalog.load_catalog()
    exported = json.loads(Path(declaration_export).read_text())
    # A retained export remains usable for documentation/tooling-only edits.
    subprocess.run([
        "git", "diff", "--exit-code", exported["revision"], "--",
        "Colib", "Colib.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain",
    ], cwd=catalog.ROOT, check=True, capture_output=True)
    declarations = {row["name"]: row for row in exported["declarations"]}
    required = {name for entry in entries for name in entry["declarations"]}
    if not required <= declarations.keys():
        raise ValueError("The native declaration export is missing catalog declarations")
    pins = {
        row["name"]: row
        for row in json.loads((catalog.ROOT / "lake-manifest.json").read_text())["packages"]
    }
    selected = {}
    for name in sorted(required):
        declaration = dict(declarations[name])
        declaration["source_url"] = catalog.source_link(
            declaration["module"], pins, exported["revision"]
        )
        selected[name] = declaration
    payload = {
        "revision": exported["revision"],
        "compiler": exported["compiler"],
        "sources": sources,
        "entries": entries,
        "declarations": selected,
    }
    output = Path(output)
    output.mkdir(parents=True, exist_ok=True)
    for name in ("index.html", "style.css", "site.js"):
        shutil.copyfile(catalog.ROOT / "docs/site" / name, output / name)
    (output / "catalog.json").write_text(
        json.dumps(payload, ensure_ascii=False, indent=2) + "\n"
    )
    (output / ".nojekyll").touch()
    print(f"Built {len(entries)} encyclopedia entries in {output}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--declarations", type=Path, default=Path("build/catalog/declarations.json"))
    parser.add_argument("--output", type=Path, default=Path("build/site"))
    args = parser.parse_args()
    build(args.declarations, args.output)
