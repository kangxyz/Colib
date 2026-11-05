#!/usr/bin/env python3
"""Check the mathematical catalog and render signatures from a built Lean environment."""

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tomllib

ROOT = Path(__file__).resolve().parents[1]
RELATIONS = {"clause", "generalization", "specialization", "adaptation", "comparison", "ingredient"}
DECLARATION = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*")


def load_catalog(root=ROOT):
    with (root / "docs/references.toml").open("rb") as stream:
        sources = tomllib.load(stream)["sources"]
    for key, source in sources.items():
        for field in ("title", "authors", "version", "url"):
            if not source.get(field):
                raise ValueError(f"Source {key} needs {field}")
    entries = []
    identifiers = set()
    for path in sorted((root / "docs/catalog").glob("*.toml")):
        with path.open("rb") as stream:
            rows = tomllib.load(stream)["entries"]
        for row in rows:
            identifier = row["id"]
            if not re.fullmatch(r"COL-[0-9]{4}", identifier) or identifier in identifiers:
                raise ValueError(f"Invalid or duplicate catalog ID {identifier}")
            identifiers.add(identifier)
            for field in ("title", "topic", "statement", "locator", "scope", "url"):
                if not isinstance(row.get(field), str) or not row[field].strip():
                    raise ValueError(f"{identifier} needs {field}")
            if row["reference"] not in sources or row.get("provenance", row["reference"]) not in sources:
                raise ValueError(f"{identifier} refers to an unknown bibliographic key")
            if row["relation"] not in RELATIONS:
                raise ValueError(f"{identifier} has an unknown correspondence relation")
            if row["review"] != "author_checked":
                raise ValueError(f"{identifier} needs a supported, explicit review status")
            declarations = row["declarations"]
            if not declarations or any(not DECLARATION.fullmatch(name) for name in declarations):
                raise ValueError(f"{identifier} needs fully qualified Lean declaration names")
            entries.append(row)
    if not entries:
        raise ValueError("The catalog is empty")
    return sources, entries


def check_sources(root=ROOT):
    """Keep the production import boundary and source-level placeholder policy explicit."""
    roots = {"Colib", "Mathlib", "StacksCore", "StacksFrontier"}
    for path in sorted((root / "Colib").rglob("*.lean")):
        source = path.read_text()
        # The production sources use ordinary nested Lean comments.
        tokens = re.split(r"(/-|-/|--[^\n]*)", source)
        depth = 0
        code = []
        for token in tokens:
            if token == "/-":
                depth += 1
            elif token == "-/":
                depth -= 1
            elif depth == 0 and not token.startswith("--"):
                code.append(token)
        if depth != 0:
            raise ValueError(f"Unbalanced comments in {path}")
        text = "".join(code)
        if re.search(r"\b(sorry|admit|axiom)\b", text):
            raise ValueError(f"Production placeholder or added axiom in {path}")
        for name in re.findall(r"(?m)^(?:public\s+)?import\s+(\S+)", text):
            if name.split(".")[0] not in roots:
                raise ValueError(f"Production import outside the dependency boundary in {path}")


def source_link(module, pins, revision):
    relative = module.replace(".", "/") + ".lean"
    provider = module.split(".")[0]
    if provider == "Colib":
        return f"https://github.com/kangxyz/colib/blob/{revision}/{relative}"
    if provider not in {"Mathlib", "StacksCore", "StacksFrontier"}:
        raise ValueError(f"Unsupported catalog source provider {provider}")
    package = "mathlib" if provider == "Mathlib" else "Stacks"
    pin = pins[package]
    return f"{pin['url'].removesuffix('.git')}/blob/{pin['rev']}/{relative}"


def build_catalog(root=ROOT):
    sources, entries = load_catalog(root)
    check_sources(root)
    names = sorted({name for entry in entries for name in entry["declarations"]})
    result = subprocess.run(
        ["lake", "env", "lean", "--run", "scripts/export_catalog.lean", *names],
        cwd=root, check=True, text=True, capture_output=True,
    )
    declarations = {row["name"]: row for row in json.loads(result.stdout)}
    if set(declarations) != set(names):
        raise ValueError("Lean returned an incomplete declaration export")
    pins = {row["name"]: row for row in json.loads((root / "lake-manifest.json").read_text())["packages"]}
    observed = subprocess.run(
        ["git", "rev-parse", "--verify", "HEAD"], cwd=root, capture_output=True, text=True,
    )
    revision = observed.stdout.strip() if observed.returncode == 0 else "main"
    revision = os.environ.get("GITHUB_SHA", revision)
    compiler = subprocess.check_output(["lake", "env", "lean", "--version"], cwd=root, text=True).strip()
    lines = [
        "# Colib encyclopedia", "",
        f"Source revision `{revision}`.", "",
        compiler, "",
        "Signatures and defining modules below were read from this built Lean environment. "
        "The correspondence notes carry their own author-review status.", "",
        "## Contents", "",
    ]
    for entry in entries:
        lines.append(f"- [{entry['id']} — {entry['title']}](#{entry['id']})")
    for entry in entries:
        reference = sources[entry["reference"]]
        lines.extend([
            "", f"<a id=\"{entry['id']}\"></a>", "",
            f"## {entry['id']} — {entry['title']}", "",
            f"**Topic** {entry['topic']}", "",
            entry["statement"], "",
            f"**Reference** [{reference['title']}]({entry['url']}), {entry['locator']}.", "",
            f"**Correspondence** {entry['relation']}. {entry['scope']}", "",
            f"**Review** {entry['review']}", "",
        ])
        if "provenance" in entry:
            source = sources[entry["provenance"]]
            lines.extend([f"**Code provenance** [{source['title']}]({source['url']}), {source['version']}.", ""])
        for name in entry["declarations"]:
            declaration = declarations[name]
            module = declaration["module"]
            lines.extend([
                f"[`{name}`]({source_link(module, pins, revision)})", "",
                "```lean", f"import {module}", f"#check {name}", "```", "",
                "```lean", declaration["type"], "```", "",
            ])
    lines.extend(["## Bibliography", ""])
    for key, source in sources.items():
        lines.extend([
            f"### {key}", "",
            f"{', '.join(source['authors'])}. [{source['title']}]({source['url']}). {source['version']}.", "",
        ])
    output = root / "build/catalog"
    output.mkdir(parents=True, exist_ok=True)
    (output / "index.md").write_text("\n".join(lines))
    (output / "declarations.json").write_text(json.dumps({
        "revision": revision, "compiler": compiler, "declarations": list(declarations.values()),
    }, ensure_ascii=False, indent=2) + "\n")
    print(f"Exported {len(entries)} entries and {len(declarations)} declarations to {output}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("check", "build"))
    arguments = parser.parse_args()
    if arguments.command == "build":
        build_catalog()
    else:
        sources, entries = load_catalog()
        check_sources()
        print(f"Checked {len(entries)} entries and {len(sources)} bibliographic records")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, tomllib.TOMLDecodeError, subprocess.CalledProcessError) as error:
        if isinstance(error, subprocess.CalledProcessError) and error.stderr:
            print(error.stderr, file=sys.stderr)
        print(f"Catalog error — {error}", file=sys.stderr)
        sys.exit(1)
