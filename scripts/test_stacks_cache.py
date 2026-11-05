"""Check the upstream-cache boundary without invoking a Lean compiler."""

import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest
from unittest.mock import patch

import stacks_cache


class StacksCacheTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.34.0-rc2\n")
        manifest = {"packages": [
            {"name": "Stacks", "rev": "a" * 40, "url": "https://github.com/AxiomMath/Stacks"},
            {"name": "mathlib", "rev": "b" * 40, "url": "https://github.com/leanprover-community/mathlib4"},
        ]}
        (self.root / "lake-manifest.json").write_text(json.dumps(manifest))
        self.build = self.root / ".lake/packages/Stacks/.lake/build"
        self.build.mkdir(parents=True)
        (self.build / "example.olean").write_bytes(b"owned compiled artifact")
        self.archive = self.root / "stacks.tar.gz"

    def pack(self):
        with patch("stacks_cache.subprocess.check_output",
                   side_effect=lambda args, **kwargs: "a" * 40 if args[-1] == "HEAD" else ""):
            stacks_cache.pack(self.archive, self.root)

    def test_common_cache_excludes_stacks(self):
        values = stacks_cache.layout(self.root)
        paths = values["environment-paths"].splitlines()
        self.assertNotIn(".lake", paths)
        self.assertNotIn(".lake/packages/Stacks", paths)
        self.assertIn(".lake/packages/mathlib", paths)

    def test_artifact_round_trip(self):
        self.pack()
        (self.build / "example.olean").unlink()
        stacks_cache.restore(self.archive, self.root)
        self.assertEqual((self.build / "example.olean").read_bytes(), b"owned compiled artifact")

    def test_mismatched_pin_is_rejected_before_writes(self):
        self.pack()
        path = self.root / "lake-manifest.json"
        manifest = json.loads(path.read_text())
        manifest["packages"][0]["rev"] = "c" * 40
        path.write_text(json.dumps(manifest))
        with self.assertRaisesRegex(ValueError, "identity mismatch"):
            stacks_cache.restore(self.archive, self.root)

    def test_path_escape_is_rejected(self):
        with tarfile.open(self.archive, "w:gz") as archive:
            info = tarfile.TarInfo("../escape")
            info.size = 1
            archive.addfile(info, io.BytesIO(b"x"))
            info = tarfile.TarInfo("metadata.json")
            info.size = 2
            archive.addfile(info, io.BytesIO(b"{}"))
        with self.assertRaisesRegex(ValueError, "regular, relative"):
            stacks_cache.restore(self.archive, self.root)


if __name__ == "__main__":
    unittest.main()
