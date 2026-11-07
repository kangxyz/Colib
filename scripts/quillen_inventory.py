#!/usr/bin/env python3
"""Reproduce the pinned Quillen module census without building or modifying sources.

This is a lexical import inventory, not a compiled declaration/result census.
Only Git object contents at the recorded commits are read; dirty worktrees are ignored.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import re
import subprocess

QUILLEN_REV = "c561118b7795eb9780be9ed391c3251d6a4d0afd"
SOURCES = {
    "quillen": (QUILLEN_REV, "https://github.com/kangxyz/quillen-k-theory"),
}


def git(repo: Path, *args: str) -> bytes:
    return subprocess.check_output(["git", "-C", str(repo), *args])


def snapshot(repo: Path, rev: str) -> dict[str, bytes]:
    """Read all tracked blobs in one batch, preserving byte-exact source hashes."""
    actual = git(repo, "rev-parse", f"{rev}^{{commit}}").decode().strip()
    if actual != rev:
        raise ValueError(f"Expected full commit {rev}, got {actual}")
    entries = []
    for entry in git(repo, "ls-tree", "-rz", "--full-tree", rev).split(b"\0"):
        if not entry:
            continue
        meta, path = entry.split(b"\t", 1)
        _, kind, oid = meta.split()
        if kind != b"blob":
            raise ValueError(f"Unsupported non-blob tree entry: {path!r}")
        entries.append((path.decode(), oid))
    result = b"" if not entries else subprocess.run(
        ["git", "-C", str(repo), "cat-file", "--batch"],
        input=b"\n".join(oid for _, oid in entries) + b"\n",
        check=True, stdout=subprocess.PIPE,
    ).stdout
    offset = 0
    files = {}
    for path, _ in entries:
        end = result.index(b"\n", offset)
        header = result[offset:end].split()
        if len(header) != 3 or header[1] != b"blob":
            raise ValueError(f"Missing blob for {path}: {header}")
        size = int(header[2])
        files[path] = result[end + 1:end + 1 + size]
        offset = end + 2 + size
    return files


def strip_comments(text: str) -> str:
    """Blank nested Lean comments and string contents, retaining source line numbers."""
    out = list(text)
    i, depth, string = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                out[i:i + 2] = "  "
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                out[i:i + 2] = "  "
                depth -= 1
                i += 2
            else:
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif string:
            if text[i] == "\\" and i + 1 < len(text):
                out[i:i + 2] = "  "
                i += 2
            else:
                if text[i] == '"':
                    string = False
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif text.startswith("/-", i):
            out[i:i + 2] = "  "
            depth = 1
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            out[i:end] = " " * (end - i)
            i = end
        elif text[i] == '"':
            out[i] = " "
            string = True
            i += 1
        else:
            i += 1
    if depth:
        raise ValueError("Unclosed block comment")
    return "".join(out)


def imports(text: str) -> list[dict]:
    """Scan import commands (including multiline lists) with source line locations.

    Lean elaboration remains authoritative. Syntax extensions and generated imports
    are not inferred. Unsupported tokens on an import line are rejected.
    """
    clean = strip_comments(text)
    rows = []
    active = False
    for lineno, line in enumerate(clean.splitlines(), 1):
        match = re.match(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(.*)$", line)
        if match:
            value = match.group(1)
            if value.startswith("all "):
                value = value[4:]
            active = True
        elif active and line.strip() and re.fullmatch(
            r"\s+(?:[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*\s*)+", line
        ) and line.split()[0] not in {
            "module", "namespace", "section", "open", "variable", "universe",
            "set_option", "noncomputable", "attribute", "export", "end",
        }:
            value = line.strip()
        elif not line.strip():
            continue
        else:
            active = False
            continue
        for name in value.split():
            if not re.fullmatch(r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*", name):
                raise ValueError(f"Unsupported import token on line {lineno}: {name}")
            rows.append({"module": name, "line": lineno})
    return rows


def category(path: str) -> str:
    root = "Quillen"
    if path == f"{root}.lean":
        return "generated_root"
    if path.startswith(f"{root}/") and path.endswith(".lean"):
        return "production"
    if path.startswith(f"{root}Test/") and path.endswith(".lean"):
        return "in_package_test"
    if path.startswith("examples/downstream/"):
        return "downstream_fixture"
    if path.startswith("scripts/"):
        return "tool"
    if path.startswith("docs/") or path.endswith(".md"):
        return "documentation"
    return "other"


def components(graph: dict[str, list[str]]) -> tuple[dict[str, int], list[list[str]]]:
    """Iterative Kosaraju; imports may exceed Python's recursion depth."""
    seen, order = set(), []
    reverse = defaultdict(list)
    for node, deps in graph.items():
        for dep in deps:
            reverse[dep].append(node)
        if node in seen:
            continue
        stack = [(node, False)]
        while stack:
            item, done = stack.pop()
            if done:
                order.append(item)
            elif item not in seen:
                seen.add(item)
                stack.append((item, True))
                stack.extend((dep, False) for dep in reversed(graph[item]) if dep not in seen)
    groups, assigned = [], set()
    for node in reversed(order):
        if node in assigned:
            continue
        group, todo = [], [node]
        while todo:
            item = todo.pop()
            if item in assigned:
                continue
            assigned.add(item)
            group.append(item)
            todo.extend(reverse[item])
        groups.append(sorted(group))
    groups.sort(key=lambda group: group[0])
    return {node: i for i, group in enumerate(groups) for node in group}, groups


def write_jsonl(path: Path, rows: list[dict]) -> None:
    path.write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in rows))


def generate(quillen: Path, output: Path,
             package_repos: dict[str, Path] | None = None) -> dict:
    if "Aglib" in (package_repos or {}):
        raise ValueError("Aglib is excluded from this inventory; do not supply its repository")
    trees = {"quillen": snapshot(quillen, QUILLEN_REV)}
    manifest = json.loads(trees["quillen"]["lake-manifest.json"])
    files, modules = [], {}
    for source, tree in trees.items():
        for path, data in sorted(tree.items()):
            row = {"source": source, "path": path, "sha256": hashlib.sha256(data).hexdigest(),
                   "category": category(path), "bytes": len(data)}
            # Census all Quillen files, including its local Quillen/Aglib/ modules.
            files.append(row)
            if path.endswith(".lean") and row["category"] in {"production", "generated_root"}:
                module = path[:-5].replace("/", ".")
                modules[module] = {**row, "module": module, "imports": imports(data.decode()),
                                   "generated_import_aggregator":
                                       b"Generated by scripts/generate_imports.py" in data}
    seeds = {name for name, row in modules.items() if row["source"] == "quillen"}
    reachable, pending = set(), list(seeds)
    while pending:
        node = pending.pop()
        if node in reachable:
            continue
        reachable.add(node)
        pending.extend(edge["module"] for edge in modules[node]["imports"]
                       if edge["module"] in modules)
    graph = {node: sorted({e["module"] for e in modules[node]["imports"]
                          if e["module"] in reachable}) for node in sorted(reachable)}
    scc, groups = components(graph)
    consumers = defaultdict(list)
    external, unresolved = [], []
    for node in graph:
        for edge in modules[node]["imports"]:
            dep = edge["module"]
            if dep in graph:
                consumers[dep].append(node)
            else:
                record = {"consumer": node, **edge}
                if dep.split(".")[0] == "Quillen":
                    unresolved.append(record)
                else:
                    external.append(record)
    package_evidence, package_modules = {}, {}
    pins = {package["name"]: package for package in manifest["packages"]}
    for package, repo in sorted((package_repos or {}).items()):
        pin = pins[package]["rev"]
        actual = git(repo, "rev-parse", f"{pin}^{{commit}}").decode().strip()
        if actual != pin:
            raise ValueError(f"Wrong {package} source revision")
        paths = git(repo, "ls-tree", "-rz", "--name-only", pin).decode().split("\0")
        for path in paths:
            if path.endswith(".lean"):
                package_modules[path[:-5].replace("/", ".")] = package
        package_evidence[package] = {"commit": pin, "method": "git ls-tree at source manifest pin"}
    for edge in external:
        if edge["module"].split(".")[0] == "Aglib":
            # Keep only Quillen's reference, never inspect the historical dependency.
            edge["source_package"] = "Aglib"
            edge["resolution"] = "unverified"
        else:
            edge["source_package"] = package_modules.get(edge["module"])
            edge["resolution"] = "source_file_verified" if edge["source_package"] else "unverified"
    # Layers and transitive imported source closure are derived from the SCC DAG.
    group_deps = {i: {scc[d] for n in g for d in graph[n] if scc[d] != i}
                  for i, g in enumerate(groups)}
    layers, closures = {}, {}
    todo = set(group_deps)
    while todo:
        ready = sorted(i for i in todo if group_deps[i] <= layers.keys())
        if not ready:
            raise ValueError("SCC condensation unexpectedly contains a cycle")
        for i in ready:
            layers[i] = 0 if not group_deps[i] else 1 + max(layers[j] for j in group_deps[i])
            closures[i] = set().union(*(closures[j] | set(groups[j]) for j in group_deps[i]))
        todo.difference_update(ready)
    ledger = []
    for name in sorted(reachable):
        row = modules[name]
        ledger.append({**row, "local_aglib_candidate": name == "Quillen.Aglib" or
                       name.startswith("Quillen.Aglib."), "scc": scc[name],
                       "dependency_tier": layers[scc[name]],
                       "transitive_source_import_count": len(closures[scc[name]] |
                                                               (set(groups[scc[name]]) - {name})),
                       "consumers": sorted(set(consumers[name])),
                       "proposed_owner": None, "target_path": None, "target_imports": [],
                       "assigned_worker": None, "disposition": None, "status": "untriaged",
                       "validation_evidence": [], "stacks_first_audit": "pending"})
    summary = {
        "schema_version": 2,
        "sources": {name: {"commit": rev, "repository": url,
                           "lean_toolchain": trees[name]["lean-toolchain"].decode().strip(),
                           "license_sha256": hashlib.sha256(trees[name]["LICENSE"]).hexdigest()}
                    for name, (rev, url) in SOURCES.items()},
        "source_packages": manifest["packages"],
        "quillen_files_by_category": dict(sorted(Counter(r["category"] for r in files
                                                         if r["source"] == "quillen").items())),
        "quillen_lean_by_category": dict(sorted(Counter(r["category"] for r in files
                               if r["source"] == "quillen" and r["path"].endswith(".lean")).items())),
        "production_including_generated_root": len(seeds),
        "generated_import_aggregators_with_marker": sum(
            modules[n]["generated_import_aggregator"] for n in seeds),
        "quillen_family_including_family_aggregator": dict(sorted(Counter(
            n.split(".")[1] for n in seeds if "." in n).items())),
        "local_aglib_candidates_including_aggregator": sum(r["local_aglib_candidate"] for r in ledger),
        "local_aglib_directory_candidates": sum(r["module"].startswith("Quillen.Aglib.") for r in ledger),
        "external_aglib_import_edges": sum(e["source_package"] == "Aglib" for e in external),
        "module_ledger_rows": len(ledger), "source_import_edges": sum(map(len, graph.values())),
        "external_import_edges": len(external), "unresolved_source_import_edges": len(unresolved),
        "strongly_connected_components": len(groups),
        "cyclic_components": [g for g in groups if len(g) > 1 or g[0] in graph[g[0]]],
        "maximum_dependency_tier": max(layers.values()),
        "closed_migration_rows": 0,
        "compiled_declaration_census": "blocked: source environment has not been built and enumerated",
        "source_package_resolution_evidence": package_evidence,
        "unverified_external_import_edges": sum(e["resolution"] == "unverified" for e in external),
        "upstream_import_resolution": "file existence only; not Lean import elaboration",
        "inventory_kind": "lexical module/import census; not a complete declaration or result ledger",
    }
    output.mkdir(parents=True, exist_ok=True)
    write_jsonl(output / "files.jsonl", files)
    write_jsonl(output / "modules.jsonl", ledger)
    write_jsonl(output / "external-imports.jsonl", external)
    write_jsonl(output / "unresolved-imports.jsonl", unresolved)
    (output / "summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    return summary


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quillen", type=Path, required=True, help="Pinned source Git repository")
    parser.add_argument("--output", type=Path, default=Path("docs/migration/quillen"))
    parser.add_argument("--package", action="append", default=[], metavar="NAME=REPO",
                        help="Verify imports against a Git repo at the source manifest pin")
    args = parser.parse_args()
    packages = {name: Path(path) for name, path in (item.split("=", 1) for item in args.package)}
    summary = generate(args.quillen, args.output, packages)
    print(json.dumps({key: value for key, value in summary.items()
                      if key not in {"source_packages", "sources"}}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
