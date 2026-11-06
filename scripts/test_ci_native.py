"""Exercise CI resource-runner exit and quiescence gates without a systemd host."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


class NativeScopeTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.bin = self.root / 'bin'
        self.bin.mkdir()
        self.command('getconf', 'case "$1" in _PHYS_PAGES) echo 4194304;; PAGE_SIZE) echo 4096;; esac')
        self.command('systemctl', 'if test "$1" = show; then echo "${CI_TEST_STATE:-inactive}"; fi')
        self.command('sleep', ':')
        self.command('sudo', '''if test "$1" = --preserve-env; then shift; fi
if test "$1" = systemd-run; then
  while test "$1" != /usr/bin/env; do shift; done
fi
exec "$@"''')
        self.env = dict(os.environ, PATH=str(self.bin) + os.pathsep + os.environ['PATH'],
                        RUNNER_TEMP=str(self.root), GITHUB_RUN_ID='1',
                        GITHUB_RUN_ATTEMPT='1', GITHUB_JOB='unit')

    def command(self, name, body):
        path = self.bin / name
        path.write_text('#!/usr/bin/env bash\nset -eu\n' + body + '\n')
        path.chmod(0o755)

    def invoke(self, *args, env=None):
        return subprocess.run(['bash', str(ROOT / '.github/ci/native.sh'), *args],
                              env=env or self.env, text=True, capture_output=True)

    def test_native_failure_is_preserved(self):
        result = self.invoke('build', 'bash', '-c', 'exit 42')
        self.assertEqual(result.returncode, 42, result.stderr)
        self.assertIn('memory=13824 MiB; threads=1; lint workers=2', result.stdout)

    def test_unstopped_scope_is_a_failed_gate(self):
        scopes = self.root / 'lean-ci-scopes/1-1-unit'
        scopes.mkdir(parents=True)
        (scopes / 'busy.scope').write_text('busy.scope\n')
        result = self.invoke('--stop', env=dict(self.env, CI_TEST_STATE='active'))
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('did not stop', result.stderr)


if __name__ == '__main__':
    unittest.main()
