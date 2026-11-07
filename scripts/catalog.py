#!/usr/bin/env python3
"""Validate and export the structured Colib Library from its editorial owners and Lean tags."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tomllib

ROOT = Path(__file__).resolve().parents[1]
RELATIONS = {
    "whole",
    "clause",
    "generalization",
    "specialization",
    "adaptation",
    "comparison",
    "ingredient",
    "background",
    "source_tag",
}
KINDS = {
    "definition",
    "lemma",
    "proposition",
    "theorem",
    "corollary",
    "example",
    "comparison",
}
SLUG = re.compile(r"[a-z][a-z0-9]*(?:-[a-z0-9]+)*")


def load_library(root=ROOT):
    with (root / "docs/references.toml").open("rb") as stream:
        sources = tomllib.load(stream)["sources"]
    for key, source in sources.items():
        if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_-]*", key):
            raise ValueError(f"Unsafe bibliographic key {key}")
        for field in ("kind", "title", "authors", "version", "url"):
            if not source.get(field):
                raise ValueError(f"Source {key} needs {field}")
        for document in source.get("documents", []):
            if not re.fullmatch(r"[0-9a-f]{64}", document.get("sha256", "")):
                raise ValueError(f"Source {key} needs an exact document hash")
    chapters, sections, entries = [], {}, {}
    for path in sorted((root / "docs/library/chapters").glob("*.toml")):
        data = tomllib.loads(path.read_text())
        chapter = data["chapter"]
        if not SLUG.fullmatch(chapter["id"]) or any(
            c["id"] == chapter["id"] for c in chapters
        ):
            raise ValueError(f"Invalid or duplicate chapter {chapter['id']}")
        if type(chapter.get("order")) is not int or chapter["order"] < 0:
            raise ValueError(
                f"Chapter {chapter['id']} needs a nonnegative integer order"
            )
        for field in ("title", "introduction"):
            if not chapter.get(field):
                raise ValueError(f"Chapter {chapter['id']} needs {field}")
        chapter["sections"] = []
        for section in data["sections"]:
            identifier = section["id"]
            if not SLUG.fullmatch(identifier) or identifier in sections:
                raise ValueError(f"Invalid or duplicate section {identifier}")
            if type(section.get("order")) is not int or section["order"] < 0:
                raise ValueError(
                    f"Section {identifier} needs a nonnegative integer order"
                )
            if "modules" in section:
                raise ValueError("Module ownership is exported from Lean")
            if not section.get("introduction"):
                raise ValueError(f"Section {identifier} needs an introduction")
            section = dict(section, chapter=chapter["id"], entries=[])
            sections[identifier] = section
            chapter["sections"].append(identifier)
        chapter["sections"].sort(
            key=lambda identifier: (sections[identifier]["order"], identifier)
        )
        chapters.append(chapter)
    for path in sorted((root / "docs/library/entries").rglob("*.toml")):
        entry = tomllib.loads(path.read_text())["entry"]
        identifier = entry["id"]
        if not re.fullmatch(r"COL-[0-9]{4,}", identifier) or identifier in entries:
            raise ValueError(f"Invalid or duplicate Library ID {identifier}")
        if any(
            field in entry
            for field in ("declarations", "reference", "locator", "requires")
        ):
            raise ValueError(
                f"{identifier} declaration bindings and citations belong in Lean attributes; dependencies come from Lean"
            )
        for field in ("title", "statement", "scope"):
            if not isinstance(entry.get(field), str) or not entry[field].strip():
                raise ValueError(f"{identifier} needs {field}")
        if type(entry.get("order")) is not int or entry["order"] < 0:
            raise ValueError(f"{identifier} needs a nonnegative integer order")
        if entry["kind"] not in KINDS or entry["section"] not in sections:
            raise ValueError(f"{identifier} has an unknown item kind or section")
        if entry["review"] != "author_checked":
            raise ValueError(
                f"{identifier} needs its supported, explicit review status"
            )
        if entry.get("provenance") and entry["provenance"] not in sources:
            raise ValueError(f"{identifier} has an unknown provenance key")
        entry["path"] = str(path.relative_to(root))
        entries[identifier] = entry
        sections[entry["section"]]["entries"].append(identifier)
    retired = {}
    for path in sorted((root / "docs/library/retired").glob("*.toml")):
        item = tomllib.loads(path.read_text())["retired"]
        identifier = item["id"]
        if (not re.fullmatch(r"COL-[0-9]{4,}", identifier)
                or identifier in entries or identifier in retired):
            raise ValueError(f"Invalid or reused retired Library ID {identifier}")
        for field in ("title", "reason"):
            if not isinstance(item.get(field), str) or not item[field].strip():
                raise ValueError(f"{identifier} needs a retirement {field}")
        if not re.fullmatch(r"[0-9a-f]{40}", item.get("previous_revision", "")):
            raise ValueError(f"{identifier} needs an exact previous revision")
        previous = Path(item.get("previous_path", ""))
        if (previous.is_absolute() or ".." in previous.parts
                or not str(previous).startswith("docs/library/entries/")
                or previous.name != identifier + ".toml"):
            raise ValueError(f"{identifier} needs its previous Library path")
        if any(value not in entries for value in item.get("related_items", [])):
            raise ValueError(f"{identifier} has an unknown related Library item")
        retired[identifier] = dict(item, status="retired", path=str(path.relative_to(root)))
    if not entries or not chapters:
        raise ValueError("The Library needs occupied mathematical chapters and items")
    for section in sections.values():
        if not section["entries"]:
            raise ValueError(f"Section {section['id']} has no mathematical items")
        section["entries"].sort(
            key=lambda identifier: (entries[identifier]["order"], identifier)
        )
    chapters.sort(key=lambda chapter: (chapter["order"], chapter["id"]))
    return {
        "sources": sources,
        "chapters": chapters,
        "sections": sections,
        "entries": entries,
        "retired": retired,
    }


def load_catalog(root=ROOT):
    """Retain the original metadata-reading API for existing tools."""
    library = load_library(root)
    return library["sources"], list(library["entries"].values())


def check_sources(root=ROOT):
    roots = {"Colib", "Mathlib", "StacksCore", "StacksFrontier"}
    for path in sorted((root / "Colib").rglob("*.lean")):
        tokens = re.split(r"(/-|-/|--[^\n]*)", path.read_text())
        depth, code = 0, []
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
        if re.search(r"\b(sorry|admit|axiom|native_decide)\b", text):
            raise ValueError(f"Production placeholder or added axiom in {path}")
        for name in re.findall(
            r"(?m)^(?:(?:public|meta)\s+)*import\s+(?:all\s+)?(\S+)", text
        ):
            if name.split(".")[0] not in roots:
                raise ValueError(
                    f"Production import outside the dependency boundary in {path}"
                )


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


def reference_url(source, locator):
    for document in source.get("documents", []):
        if document.get("locator_prefix") and locator.startswith(
            document["locator_prefix"]
        ):
            return document["url"]
    return source["url"]


def compile_library(library, native, pins, revision):
    entries = {
        identifier: dict(
            entry, declarations=[], references=[], used_by=[], formal_dependencies=[]
        )
        for identifier, entry in library["entries"].items()
    }
    declarations = {row["name"]: dict(row) for row in native["declarations"]}
    memberships = {}
    for binding in native["bindings"]:
        identifier, name = binding["id"], binding["name"]
        if identifier not in entries or name not in declarations:
            raise ValueError(f"Unknown compiled Library binding {identifier} / {name}")
        if name not in entries[identifier]["declarations"]:
            entries[identifier]["declarations"].append(name)
        memberships.setdefault(name, set()).add(identifier)
    for entry in entries.values():
        if not entry["declarations"]:
            raise ValueError(
                f"{entry['id']} needs a compiled @[colib_tag] declaration binding"
            )
    citations = list(native["citations"])
    citations.extend(
        {
            "name": row["name"],
            "source": "stacks",
            "locator": "Tag " + row["tag"],
            "relation": "source_tag",
            "scope": row["scope"],
            "url": "https://stacks.math.columbia.edu/tag/" + row["tag"],
        }
        for row in native["stacks"]
    )
    resolved_citations = []
    for citation in citations:
        if citation["name"] not in declarations:
            raise ValueError("A native citation needs its declaring Lean constant")
        key = citation["source"]
        if key not in library["sources"]:
            raise ValueError(f"Unknown bibliographic key {key} on {citation['name']}")
        if not citation["locator"].strip() or citation["relation"] not in RELATIONS:
            raise ValueError(
                f"Invalid literature locator or relation on {citation['name']}"
            )
        citation = dict(citation)
        citation["url"] = citation.get(
            "url", reference_url(library["sources"][key], citation["locator"])
        )
        resolved_citations.append(citation)
        for identifier in memberships.get(citation["name"], set()):
            entries[identifier]["references"].append(citation)
    for name, declaration in declarations.items():
        declaration["source_url"] = source_link(declaration["module"], pins, revision)
        targets = {
            identifier
            for dependency in declaration.get("dependencies", [])
            for identifier in memberships.get(dependency, set())
        }
        for identifier in memberships.get(name, set()):
            entries[identifier]["formal_dependencies"].extend(targets - {identifier})
    for entry in entries.values():
        if not entry["references"]:
            raise ValueError(f"{entry['id']} needs a compiled precise source reference")
        entry["declarations"].sort()
        entry["formal_dependencies"] = sorted(set(entry["formal_dependencies"]))
    for entry in entries.values():
        for dependency in entry["formal_dependencies"]:
            entries[dependency]["used_by"].append(entry["id"])
    sections = {key: dict(value) for key, value in library["sections"].items()}
    for section in sections.values():
        section["modules"] = sorted(
            {
                declarations[name]["module"]
                for identifier in section["entries"]
                for name in entries[identifier]["declarations"]
            }
        )
    modules = {
        row["name"]: dict(row, source_url=source_link(row["name"], pins, revision))
        for row in native["modules"]
    }
    return dict(
        library,
        schema=2,
        revision=revision,
        sections=sections,
        entries=entries,
        declarations=declarations,
        modules=modules,
        citations=resolved_citations,
    )


def source_hashes(root=ROOT):
    paths = [
        root / "Colib.lean",
        root / "lakefile.toml",
        root / "lake-manifest.json",
        root / "lean-toolchain",
    ]
    paths.extend((root / "Colib").rglob("*.lean"))
    return {
        str(path.relative_to(root)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in sorted(paths)
    }


def render_markdown(library):
    lines = ["# Colib Library", "", f"Source revision `{library['revision']}`.", ""]
    for chapter in library["chapters"]:
        lines.extend(["## " + chapter["title"], "", chapter["introduction"], ""])
        for section_id in chapter["sections"]:
            section = library["sections"][section_id]
            lines.extend(["### " + section["title"], "", section["introduction"], ""])
            for identifier in section["entries"]:
                entry = library["entries"][identifier]
                lines.extend(
                    [
                        f'<a id="{identifier}"></a>',
                        "",
                        f"#### {identifier} — {entry['kind'].title()}. {entry['title']}",
                        "",
                        entry["statement"],
                        "",
                        entry["scope"],
                        "",
                        "Direct Lean references — "
                        + (", ".join(entry["formal_dependencies"]) or "None"),
                        "",
                    ]
                )
                for citation in entry["references"]:
                    source = library["sources"][citation["source"]]
                    lines.extend(
                        [
                            f"- [{source['title']}]({citation['url']}), {citation['locator']}. "
                            f"{citation['relation']}. {citation['scope']}"
                        ]
                    )
                lines.append("")
                for name in entry["declarations"]:
                    declaration = library["declarations"][name]
                    lines.extend(
                        [
                            f"[`{name}`]({declaration['source_url']})",
                            "",
                            "```lean",
                            "import " + declaration["module"],
                            "#check " + name,
                            "```",
                            "",
                            "```lean",
                            declaration["type"],
                            "```",
                            "",
                        ]
                    )
    return "\n".join(lines)


def build_catalog(root=ROOT):
    editorial = load_library(root)
    check_sources(root)
    result = subprocess.run(
        ["lake", "env", "lean", "scripts/export_catalog.lean"],
        cwd=root,
        check=True,
        text=True,
        capture_output=True,
    )
    native = json.loads(result.stdout)
    pins = {
        row["name"]: row
        for row in json.loads((root / "lake-manifest.json").read_text())["packages"]
    }
    observed = subprocess.run(
        ["git", "rev-parse", "--verify", "HEAD"],
        cwd=root,
        capture_output=True,
        text=True,
    )
    revision = os.environ.get("GITHUB_SHA", observed.stdout.strip() or "main")
    library = compile_library(editorial, native, pins, revision)
    library["compiler"] = subprocess.check_output(
        ["lake", "env", "lean", "--version"], cwd=root, text=True
    ).strip()
    library["source_hashes"] = source_hashes(root)
    output = root / "build/library"
    output.mkdir(parents=True, exist_ok=True)
    (output / "index.md").write_text(render_markdown(library))
    (output / "library.json").write_text(
        json.dumps(library, ensure_ascii=False, indent=2) + "\n"
    )
    (output / "declarations.json").write_text(
        json.dumps(
            dict(
                native,
                revision=revision,
                compiler=library["compiler"],
                source_hashes=library["source_hashes"],
            ),
            ensure_ascii=False,
            indent=2,
        )
        + "\n"
    )
    # Preserve the original generated-output paths for existing release consumers.
    legacy = root / "build/catalog"
    legacy.mkdir(parents=True, exist_ok=True)
    for filename in ("index.md", "declarations.json"):
        shutil.copyfile(output / filename, legacy / filename)
    print(
        f"Exported {len(library['entries'])} Library items and {len(library['declarations'])} indexed declarations"
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("check", "build", "show"))
    parser.add_argument("identifier", nargs="?")
    args = parser.parse_args()
    if args.command == "build":
        build_catalog()
    elif args.command == "show":
        library = load_library()
        if args.identifier in library["retired"]:
            print(json.dumps(library["retired"][args.identifier], ensure_ascii=False, indent=2))
            return
        if args.identifier not in library["entries"]:
            raise ValueError("Select an existing permanent Library ID")
        entry = library["entries"][args.identifier]
        section = library["sections"][entry["section"]]
        data = dict(entry, chapter=section["chapter"])
        export = ROOT / "build/library/library.json"
        if export.exists():
            built = json.loads(export.read_text())
            if built.get("source_hashes") == source_hashes():
                data["declarations"] = built["entries"][args.identifier]["declarations"]
                data["modules"] = sorted(
                    {
                        built["declarations"][name]["module"]
                        for name in data["declarations"]
                    }
                )
        print(json.dumps(data, ensure_ascii=False, indent=2))
    else:
        library = load_library()
        check_sources()
        print(
            f"Checked {len(library['chapters'])} chapters, {len(library['sections'])} sections and "
            f"{len(library['entries'])} permanent items"
        )


if __name__ == "__main__":
    try:
        main()
    except (
        ValueError,
        KeyError,
        tomllib.TOMLDecodeError,
        subprocess.CalledProcessError,
    ) as error:
        if isinstance(error, subprocess.CalledProcessError):
            for output in (error.stdout, error.stderr):
                if output:
                    print(output, file=sys.stderr)
        print(f"Library error — {error}", file=sys.stderr)
        sys.exit(1)
