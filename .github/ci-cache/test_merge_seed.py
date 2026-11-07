"""Check merge-seed eligibility and reject malformed transport inputs."""

from io import BytesIO
import json
from pathlib import Path
import tarfile
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch
import zipfile

from merge_seed import download, find_seed, sha, unpack_native, validate_producer

HEAD = '1' * 40
BRANCH = '2' * 40
BASE = '3' * 40
TREE = '4' * 40
REPOSITORY = 27


def run(commit=HEAD):
    return dict(id=10, head_sha=commit, head_branch='work/feature', event='push',
                status='completed', conclusion='success', path='.github/workflows/ci.yml',
                repository={'id': REPOSITORY}, head_repository={'id': REPOSITORY},
                updated_at='2026-11-07T10:00:00Z')


def artifact(commit=HEAD, name='cache-staging'):
    return dict(id=4, name=name, size_in_bytes=4096, expired=False, digest='sha256:' + 'b'*64,
                workflow_run=dict(id=10, head_sha=commit, repository_id=REPOSITORY,
                                  head_repository_id=REPOSITORY))


class SelectMergeSeed(unittest.TestCase):
    def select(self, *, runs, artifacts=(), parents=(), trees=None, pulls=()):
        requests = []
        trees = trees or {}

        def api(path, **parameters):
            requests.append((path, parameters))
            if path == 'actions/workflows/ci.yml/runs':
                return {'workflow_runs': runs.get(parameters['head_sha'], [])}
            if path == 'actions/runs/11':
                return {'created_at': '2026-11-07T10:01:00Z'}
            if path == 'actions/runs/10/artifacts':
                return {'artifacts': artifacts}
            if path == f'commits/{HEAD}/pulls':
                return pulls
            if path.startswith('git/commits/'):
                return {'tree': {'sha': trees[path.rsplit('/', 1)[-1]]}}
            self.fail('Unexpected API request: ' + path)

        return find_seed(api, HEAD, TREE, 'main', REPOSITORY, 11, parents), requests

    def test_fast_forward_uses_only_prior_trusted_branch_run(self):
        actual = run()
        candidates = [
            {**actual, 'head_branch': 'main'},
            {**actual, 'head_repository': {'id': 91}},
            {**actual, 'event': 'pull_request'},
            {**actual, 'updated_at': '2026-11-07T10:02:00Z'},
            actual,
        ]
        result, requests = self.select(runs={HEAD: candidates}, artifacts=[artifact()])
        self.assertEqual(result, (actual, {'cache-staging': artifact()}))
        self.assertEqual([path for path, _ in requests].count('actions/runs/10/artifacts'), 1)
        self.assertNotIn((f'commits/{HEAD}/pulls', {'per_page': 20}), requests)

    def test_true_merge_checks_source_tree_before_looking_up_branch_run(self):
        for source_tree in (TREE, BASE):
            with self.subTest(source_tree=source_tree):
                result, requests = self.select(runs={BRANCH: [run(BRANCH)]},
                                               artifacts=[artifact(BRANCH)],
                                               parents=(BASE, BRANCH), trees={BRANCH: source_tree})
                branch_lookup = any(params.get('head_sha') == BRANCH for _, params in requests)
                self.assertEqual(branch_lookup, source_tree == TREE)
                self.assertEqual(result is not None, source_tree == TREE)

    def test_squash_requires_recorded_same_repository_merge_into_target(self):
        pull = dict(merged_at='2026-11-07T10:01:00Z', merge_commit_sha=HEAD,
                    head={'sha': BRANCH, 'repo': {'id': REPOSITORY}},
                    base={'ref': 'main', 'repo': {'id': REPOSITORY}})
        for update, expected in [
            ({}, True),
            ({'head': {'sha': BRANCH, 'repo': {'id': 91}}}, False),
            ({'base': {'ref': 'other', 'repo': {'id': REPOSITORY}}}, False),
            ({'merge_commit_sha': BASE}, False),
        ]:
            result, _ = self.select(runs={BRANCH: [run(BRANCH)]}, artifacts=[artifact(BRANCH)],
                                    parents=(BASE,), trees={BRANCH: TREE}, pulls=[{**pull, **update}])
            self.assertEqual(result is not None, expected)

    def test_normal_push_and_unbound_artifacts_do_not_have_a_seed(self):
        result, _ = self.select(runs={}, parents=(BASE,))
        self.assertIsNone(result)
        valid = artifact()
        candidates = [
            {**valid, 'expired': True},
            {**valid, 'digest': None},
            {**valid, 'workflow_run': {**valid['workflow_run'], 'head_sha': BRANCH}},
        ]
        result, _ = self.select(runs={HEAD: [run()]}, artifacts=candidates)
        self.assertIsNone(result)


class MergeSeedTransport(unittest.TestCase):
    def test_native_stage_rejects_links_paths_and_wrong_producer(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for name in ('../outside', './8d42f7abb1e3f124.ltar'):
                archive = root / 'bad.tar'
                with tarfile.open(archive, 'w') as tar:
                    member = tarfile.TarInfo(name)
                    if name.startswith('./'):
                        member.type = tarfile.SYMTYPE
                        member.linkname = '../outside'
                        tar.addfile(member)
                    else:
                        member.size = 1
                        tar.addfile(member, BytesIO(b'x'))
                staging = root / f'stage-{len(list(root.iterdir()))}'
                with self.assertRaises(ValueError):
                    unpack_native(archive, staging)
                self.assertFalse((root / 'outside').exists())

            staging = root / 'verified'
            staging.mkdir()
            producer = dict(repository='kangxyz/colib', revision=HEAD, package='Colib',
                            domain='Linux-X64-pin', compiler='pinned Lean')
            (staging / 'producer.json').write_text(json.dumps(producer))
            validate_producer(staging, 'kangxyz/colib', HEAD, 'Colib', 'Linux-X64-pin', 'pinned Lean')
            with self.assertRaises(ValueError):
                validate_producer(staging, 'kangxyz/colib', BRANCH, 'Colib', 'Linux-X64-pin', 'pinned Lean')

    def test_download_binds_digest_and_extracts_only_expected_file(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / 'source.zip'
            with zipfile.ZipFile(source, 'w') as archive:
                archive.writestr('lake-native-cache.tar', b'expected data')
            for digest, expected in [('sha256:' + sha(source), True), ('sha256:' + 'c'*64, False)]:
                target = root / str(expected)
                target.mkdir()
                record = {**artifact(), 'digest': digest, 'size_in_bytes': source.stat().st_size}

                def serve(command, *, stdout, check):
                    self.assertEqual(command[-1], 'repos/kangxyz/colib/actions/artifacts/4/zip')
                    stdout.write(source.read_bytes())

                with patch('merge_seed.subprocess.run', side_effect=serve), patch(
                        'merge_seed.shutil.disk_usage', return_value=SimpleNamespace(free=2 * 1024**3)):
                    if expected:
                        result = download('kangxyz/colib', record, target, 'lake-native-cache.tar')
                        self.assertEqual(result.read_bytes(), b'expected data')
                        self.assertFalse((target / 'artifact.zip').exists())
                    else:
                        with self.assertRaises(ValueError):
                            download('kangxyz/colib', record, target, 'lake-native-cache.tar')
                        self.assertFalse((target / 'lake-native-cache.tar').exists())


if __name__ == '__main__':
    unittest.main()
