"""Focused regression tests for the historical Quillen inventory tooling."""

from pathlib import Path
import subprocess
import tempfile
import unittest

from quillen_inventory import category, components, imports, snapshot, strip_comments


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
        self.assertEqual(category('Quillen.lean', 'quillen'), 'generated_root')
        self.assertEqual(category('Quillen/Aglib/Basic.lean', 'quillen'), 'production')
        self.assertEqual(category('QuillenTest/Basic.lean', 'quillen'), 'in_package_test')
        self.assertEqual(category('examples/downstream/Consumer.lean', 'quillen'),
                         'downstream_fixture')

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
