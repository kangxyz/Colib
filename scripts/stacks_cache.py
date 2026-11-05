#!/usr/bin/env python3
"""Keep the pinned Stacks dependency cache separate from Colib artifacts."""

import argparse
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import platform
import subprocess
import tarfile
import tempfile
import shutil

ROOT = Path(__file__).resolve().parents[1]


def context(root=ROOT):
    manifest = json.loads((root / "lake-manifest.json").read_text())
    packages = manifest["packages"]
    stacks = next(package for package in packages if package["name"] == "Stacks")
    architecture = os.environ.get("RUNNER_ARCH", platform.machine()).lower()
    architecture = {"x64": "x86_64", "arm64": "aarch64"}.get(architecture, architecture)
    system = os.environ.get("RUNNER_OS", platform.system()).lower()
    system = {"macos": "darwin"}.get(system, system)
    identity = {
        "schema": 1,
        "stacks_revision": stacks["rev"],
        "toolchain": (root / "lean-toolchain").read_text().strip(),
        "platform": f"{system}-{architecture}",
        "packages": sorted(
            (package["name"], package["rev"], package["url"]) for package in packages
        ),
    }
    identity["packages"] = [list(package) for package in identity["packages"]]
    return identity


def layout(root=ROOT):
    manifest = json.loads((root / "lake-manifest.json").read_text())
    names = [package["name"] for package in manifest["packages"]]
    if any(not name or any(c not in "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_-" for c in name)
           for name in names):
        raise ValueError("Cache package names must be plain directory names")
    paths = [".lake/build", ".lake/config", ".lake/tools"]
    paths.extend(f".lake/packages/{name}" for name in names if name != "Stacks")
    identity = context(root)
    checksum = hashlib.sha256(json.dumps(identity, sort_keys=True).encode()).hexdigest()
    return {
        "environment-paths": "\n".join(paths),
        "stacks-path": ".lake/packages/Stacks",
        "stacks-context": checksum,
        "stacks-revision": identity["stacks_revision"],
    }


def pack(destination, root=ROOT):
    identity = context(root)
    package = root / ".lake/packages/Stacks"
    revision = subprocess.check_output(
        ["git", "-C", str(package), "rev-parse", "HEAD"], text=True
    ).strip()
    if revision != identity["stacks_revision"]:
        raise ValueError("Stacks checkout differs from the manifest pin")
    dirty = subprocess.check_output(
        ["git", "-C", str(package), "status", "--porcelain", "--untracked-files=no"], text=True
    ).strip()
    if dirty:
        raise ValueError("Commit or restore tracked Stacks source changes before exporting")
    build = package / ".lake/build"
    if not build.is_dir():
        raise ValueError("Build the selected Stacks imports before exporting their artifacts")
    native = Path(os.environ.get("LAKE_CACHE_DIR", root / ".lake")).resolve()
    files = {}
    payloads = []
    for path in sorted(build.rglob("*")):
        resolved = path.resolve()
        if not resolved.is_relative_to(build.resolve()) and not resolved.is_relative_to(native):
            raise ValueError(f"Artifact resolves outside owned build/cache roots — {path}")
        if path.is_dir():
            continue
        if not path.is_file():
            raise ValueError(f"Unsupported artifact — {path}")
        name = path.relative_to(build).as_posix()
        before = path.stat()
        with path.open("rb") as stream:
            files[name] = hashlib.file_digest(stream, "sha256").hexdigest()
        payloads.append((name, path, before))
    if not files:
        raise ValueError("The selected Stacks artifact set is empty")
    metadata = dict(identity, files=files)
    destination = Path(destination)
    destination.parent.mkdir(parents=True, exist_ok=True)
    with tarfile.open(destination, "w:gz") as archive:
        raw = json.dumps(metadata, sort_keys=True).encode()
        entry = tarfile.TarInfo("metadata.json")
        entry.size = len(raw)
        archive.addfile(entry, io.BytesIO(raw))
        for name, path, before in payloads:
            entry = tarfile.TarInfo("build/" + name)
            entry.size, entry.mtime, entry.mode = before.st_size, int(before.st_mtime), before.st_mode & 0o777
            with path.open("rb") as stream:
                archive.addfile(entry, stream)
            after = path.stat()
            if (before.st_ino, before.st_size, before.st_mtime_ns) != (
                after.st_ino, after.st_size, after.st_mtime_ns
            ):
                raise ValueError(f"Stacks artifact changed during export — {name}")
    print(f"Exported {len(files)} Stacks artifact files to {destination}")


def restore(source, root=ROOT):
    identity = context(root)
    build = root / ".lake/packages/Stacks/.lake/build"
    (root / ".lake").mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="stacks-import-", dir=root / ".lake") as directory:
        staging = Path(directory)
        with tarfile.open(source, "r:gz") as archive:
            members = archive.getmembers()
            names = [member.name for member in members]
            if len(names) != len(set(names)) or names.count("metadata.json") != 1:
                raise ValueError("Duplicate or missing cache metadata")
            for member in members:
                path = PurePosixPath(member.name)
                if (not member.isfile() or path.is_absolute() or ".." in path.parts
                        or str(path) != member.name or "\\" in member.name or ":" in member.name):
                    raise ValueError("The cache may contain only regular, relative artifact files")
                if member.name != "metadata.json" and not member.name.startswith("build/"):
                    raise ValueError("Unexpected Stacks cache member")
            metadata = json.load(archive.extractfile("metadata.json"))
            for key, value in identity.items():
                if metadata.get(key) != value:
                    raise ValueError(f"Stacks cache identity mismatch — {key}")
            restored = set()
            for member in members:
                if member.name == "metadata.json":
                    continue
                name = member.name.removeprefix("build/")
                target = staging / name
                target.parent.mkdir(parents=True, exist_ok=True)
                with archive.extractfile(member) as incoming, target.open("wb") as stream:
                    shutil.copyfileobj(incoming, stream)
                with target.open("rb") as stream:
                    digest = hashlib.file_digest(stream, "sha256").hexdigest()
                if digest != metadata["files"].get(name):
                    raise ValueError(f"Stacks artifact digest mismatch — {name}")
                os.utime(target, (member.mtime, member.mtime))
                os.chmod(target, member.mode & 0o777)
                restored.add(name)
            if restored != set(metadata["files"]):
                raise ValueError("Incomplete Stacks artifact archive")
        # Validate all destinations before installing the verified files.
        for name in restored:
            for parent in (build / name).parents:
                if parent == root.parent:
                    break
                if parent.is_symlink():
                    raise ValueError("Stacks artifact parents must be ordinary directories")
        for name in restored:
            target = build / name
            target.parent.mkdir(parents=True, exist_ok=True)
            os.replace(staging / name, target)
    print(f"Restored {len(restored)} Stacks artifact files. Native builds check applicability")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    describe = commands.add_parser("layout")
    describe.add_argument("--github-output", type=Path)
    for command in ("pack", "restore"):
        commands.add_parser(command).add_argument("archive", type=Path)
    args = parser.parse_args()
    if args.command == "layout":
        values = layout()
        if args.github_output:
            with args.github_output.open("a") as stream:
                for key, value in values.items():
                    stream.write(f"{key}<<COLIB_CACHE_VALUE\n{value}\nCOLIB_CACHE_VALUE\n")
        else:
            print(json.dumps(values, indent=2))
    elif args.command == "pack":
        pack(args.archive)
    else:
        restore(args.archive)


if __name__ == "__main__":
    main()
