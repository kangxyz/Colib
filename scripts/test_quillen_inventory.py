"""Focused regression tests for the historical Quillen inventory tooling."""

from pathlib import Path
import json
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from quillen_inventory import (QUILLEN_REV, category, components, generate, imports,
                              snapshot, strip_comments)


class QuillenInventoryTests(unittest.TestCase):
    def test_imports_ignore_nested_comments_and_strings(self):
        text = ('/- import Wrong /- import Nested -/ -/\nmodule\n'
                'public import Foo.Bar -- import Wrong\n'
                'private meta import Baz\n'
                'def text := "import Wrong"\n')
        self.assertEqual(imports(text), [{"module": "Foo.Bar", "line": 3},
                                         {"module": "Baz", "line": 4}])

    def test_import_all_is_a_modifier(self):
        self.assertEqual(imports('import all Mathlib.Example\n'),
                         [{"module": "Mathlib.Example", "line": 1}])

    def test_multiline_imports_and_namespaces(self):
        self.assertEqual(imports('import Foo\n  Bar.Baz\n\nnamespace Q\n'),
                         [{"module": "Foo", "line": 1}, {"module": "Bar.Baz", "line": 2}])

    def test_unterminated_comment_fails(self):
        with self.assertRaises(ValueError):
            strip_comments('/- broken')

    def test_categories_do_not_double_count_root(self):
        self.assertEqual(category('Quillen.lean'), 'generated_root')
        self.assertEqual(category('Quillen/Aglib/Basic.lean'), 'production')
        self.assertEqual(category('QuillenTest/Basic.lean'), 'in_package_test')
        self.assertEqual(category('examples/downstream/Consumer.lean'),
                         'downstream_fixture')

    def test_generate_reads_only_quillen_and_retains_local_aglib(self):
        tree = {
            "LICENSE": b"Apache-2.0",
            "lean-toolchain": b"leanprover/lean4:v4.34.1",
            "lake-manifest.json": json.dumps({"packages": []}).encode(),
            "Quillen.lean": b"import Quillen.Aglib.Basic\n",
            "Quillen/Aglib/Basic.lean": b"import Aglib.Old Quillen.Missing Mathlib.Test\n",
        }
        with tempfile.TemporaryDirectory() as directory, patch(
            'quillen_inventory.snapshot', return_value=tree
        ) as read:
            output = Path(directory)
            summary = generate(Path('quillen-only'), output)
            read.assert_called_once_with(Path('quillen-only'), QUILLEN_REV)
            rows = [json.loads(line) for line in (output / 'modules.jsonl').read_text().splitlines()]
            self.assertEqual([row['module'] for row in rows], ['Quillen', 'Quillen.Aglib.Basic'])
            self.assertTrue(all(row['source'] == 'quillen' for row in rows))
            self.assertEqual(rows[0]['transitive_source_import_count'], 1)
            self.assertEqual(rows[1]['dependency_tier'], 0)
            external = [json.loads(line) for line in (output / 'external-imports.jsonl').read_text().splitlines()]
            self.assertEqual(external[0], {'consumer': 'Quillen.Aglib.Basic', 'module': 'Aglib.Old',
                                          'line': 1, 'source_package': 'Aglib', 'resolution': 'unverified'})
            unresolved = [json.loads(line) for line in (output / 'unresolved-imports.jsonl').read_text().splitlines()]
            self.assertEqual([row['module'] for row in unresolved], ['Quillen.Missing'])
            self.assertEqual(summary['module_ledger_rows'], 2)
            self.assertEqual(summary['external_aglib_import_edges'], 1)
            self.assertEqual(summary['unverified_external_import_edges'], 2)
            self.assertEqual(set(summary['sources']), {'quillen'})
            self.assertEqual(summary['source_packages'], [])

    def test_checked_in_inventory_contains_only_quillen(self):
        directory = Path(__file__).resolve().parents[1] / 'docs/migration/quillen'
        def read(name):
            return [json.loads(line) for line in (directory / name).read_text().splitlines()]
        files, modules = read('files.jsonl'), read('modules.jsonl')
        self.assertEqual(len(files), 8053)
        self.assertEqual(len(modules), 5833)
        self.assertEqual({row['source'] for row in files + modules}, {'quillen'})
        self.assertEqual(sum(row['local_aglib_candidate'] for row in modules), 837)
        names = {row['module'] for row in modules}
        external = read('external-imports.jsonl')
        self.assertTrue(all(row['consumer'] in names and row['module'] not in names
                            for row in external))
        aglib = [row for row in external if row['module'].startswith('Aglib.')]
        self.assertEqual(len(aglib), 2632)
        self.assertTrue(all(row['resolution'] == 'unverified' for row in aglib))
        self.assertTrue(all(set(row['consumers']) <= names for row in modules))
        summary = json.loads((directory / 'summary.json').read_text())
        self.assertEqual(summary['schema_version'], 2)
        self.assertEqual(set(summary['sources']), {'quillen'})
        self.assertEqual(summary['external_import_edges'], len(external))
        self.assertEqual(summary['module_ledger_rows'], len(modules))

    def test_aglib_package_is_rejected_before_reading_any_repository(self):
        with patch('quillen_inventory.snapshot') as read, patch('quillen_inventory.git') as git:
            with self.assertRaisesRegex(ValueError, 'Aglib is excluded'):
                generate(Path('quillen'), Path('output'), {'Aglib': Path('must-not-be-read')})
            read.assert_not_called()
            git.assert_not_called()

    def test_scc_handles_cycles_and_diamonds(self):
        graph = {'a': ['b', 'c'], 'b': ['d'], 'c': ['d'], 'd': [], 'e': ['f'], 'f': ['e']}
        owners, groups = components(graph)
        self.assertEqual(groups, [['a'], ['b'], ['c'], ['d'], ['e', 'f']])
        self.assertEqual(owners['e'], owners['f'])
        self.assertNotEqual(owners['a'], owners['d'])

    def test_snapshot_ignores_dirty_worktree(self):
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            def run(*args):
                return subprocess.check_output(['git', '-C', str(repo), *args],
                                               stderr=subprocess.DEVNULL)
            run('init')
            (repo / 'file.lean').write_text('import Original\n')
            run('add', 'file.lean')
            run('-c', 'user.name=Inventory Test', '-c', 'user.email=test@example.invalid',
                'commit', '-m', 'fixture')
            rev = run('rev-parse', 'HEAD').decode().strip()
            (repo / 'file.lean').write_text('import Dirty\n')
            self.assertEqual(snapshot(repo, rev), {'file.lean': b'import Original\n'})


if __name__ == '__main__':
    unittest.main()
