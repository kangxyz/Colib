#!/usr/bin/env python3
"""Warm a Colib merge build from an already checked same-repository branch."""

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import tomllib
from urllib.parse import urlencode
import zipfile

COMMIT = re.compile(r'[0-9a-f]{40}')
DIGEST = re.compile(r'sha256:[0-9a-f]{64}')
NATIVE_FILE = re.compile(r'[0-9a-f]{16}(?:\.[A-Za-z0-9._+-]+)?')
ARTIFACTS = {'cache-staging', 'build-dependencies', 'build-stacks'}


def output(*command):
    return subprocess.check_output(command, text=True).strip()


def sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def github(repository, endpoint, **parameters):
    query = '?' + urlencode(parameters) if parameters else ''
    return json.loads(output('gh', 'api', f'repos/{repository}/{endpoint}{query}'))


def source_commits(api, head, target, repository_id, parents):
    # A fast-forward may have the same single-parent head as a direct push.
    yield head
    if len(parents) == 2:
        yield parents[1]
    for pull in api(f'commits/{head}/pulls', per_page=20):
        source, base = pull.get('head', {}), pull.get('base', {})
        if (pull.get('merged_at') and pull.get('merge_commit_sha') == head
                and base.get('ref') == target
                and (base.get('repo') or {}).get('id') == repository_id
                and (source.get('repo') or {}).get('id') == repository_id):
            yield source.get('sha', '')


def find_seed(api, head, tree, target, repository_id, run_id, parents):
    seen = set()
    started = None
    for commit in source_commits(api, head, target, repository_id, parents):
        if not COMMIT.fullmatch(commit) or commit in seen:
            continue
        seen.add(commit)
        if commit != head and api(f'git/commits/{commit}')['tree']['sha'] != tree:
            continue
        for run in api('actions/workflows/ci.yml/runs', head_sha=commit,
                       event='push', status='success', per_page=10)['workflow_runs']:
            if (run.get('head_sha') != commit or run.get('event') != 'push'
                    or run.get('path') != '.github/workflows/ci.yml'
                    or run.get('status') != 'completed' or run.get('conclusion') != 'success'
                    or not run.get('head_branch') or run['head_branch'] == target
                    or (run.get('repository') or {}).get('id') != repository_id
                    or (run.get('head_repository') or {}).get('id') != repository_id):
                continue
            if started is None:
                started = api(f'actions/runs/{run_id}')['created_at']
            if not run.get('updated_at') or run['updated_at'] > started:
                continue
            artifacts = {}
            for item in api(f'actions/runs/{run["id"]}/artifacts', per_page=100)['artifacts']:
                origin = item.get('workflow_run') or {}
                name = item.get('name')
                if (name not in ARTIFACTS or item.get('expired') is not False
                        or origin.get('id') != run['id'] or origin.get('head_sha') != commit
                        or origin.get('repository_id') != repository_id
                        or origin.get('head_repository_id') != repository_id
                        or not DIGEST.fullmatch(item.get('digest') or '')
                        or type(item.get('id')) is not int or item['id'] <= 0
                        or type(item.get('size_in_bytes')) is not int or item['size_in_bytes'] <= 0):
                    continue
                if name in artifacts:
                    raise ValueError('multiple eligible artifacts named ' + name)
                artifacts[name] = item
            if 'cache-staging' in artifacts:
                return run, artifacts
    return None


def download(repository, item, directory, filename):
    # Keep each ZIP and its extracted checkpoint in a disposable directory.
    if shutil.disk_usage(directory).free < 3 * item['size_in_bytes'] + 512 * 1024**2:
        raise ValueError('insufficient temporary space for ' + item['name'])
    archive = directory / 'artifact.zip'
    with archive.open('xb') as target:
        subprocess.run(['gh', 'api', f'repos/{repository}/actions/artifacts/{item["id"]}/zip'],
                       stdout=target, check=True)
    if 'sha256:' + sha(archive) != item['digest']:
        raise ValueError('artifact digest mismatch for ' + item['name'])
    destination = directory / filename
    with zipfile.ZipFile(archive) as compressed:
        entries = compressed.infolist()
        if len(entries) != 1 or entries[0].filename != filename or entries[0].is_dir():
            raise ValueError('unexpected artifact member for ' + item['name'])
        with compressed.open(entries[0]) as source, destination.open('xb') as target:
            shutil.copyfileobj(source, target)
    archive.unlink()
    return destination


def unpack_native(archive, staging):
    staging.mkdir()
    with tarfile.open(archive, 'r:') as tar:
        for member in tar:
            name = member.name.removeprefix('./')
            if member.isdir() and name in ('', '.'):
                continue
            if not member.isreg() or (name not in ('outputs.jsonl', 'producer.json')
                                      and not NATIVE_FILE.fullmatch(name)):
                raise ValueError('unexpected native staging member ' + member.name)
            with tar.extractfile(member) as source, (staging / name).open('xb') as target:
                shutil.copyfileobj(source, target)


def validate_producer(staging, repository, revision, package, domain, compiler):
    producer = json.loads((staging / 'producer.json').read_text())
    expected = dict(repository=repository, revision=revision, package=package,
                    domain=domain, compiler=compiler)
    if any(producer.get(key) != value for key, value in expected.items()):
        raise ValueError('native artifact producer does not match the verified branch build')


def restore_layer(layer, archive, native_cache):
    receipt = Path('.lake/ci-cache') / (layer + '.json')
    try:
        restored = json.loads(receipt.read_text())
    except (OSError, ValueError):
        restored = {}
    if isinstance(restored, dict) and restored.get('archive_sha256') == sha(archive):
        print(f'{layer} already restored from the identical archive', flush=True)
        return
    subprocess.run([sys.executable, '.github/ci-cache/checkpoint.py', 'restore',
                    '--root', '.', '--layer', layer, '--input', str(archive),
                    '--native-cache', native_cache], check=True)


def main():
    repository = os.environ['GITHUB_REPOSITORY']
    repository_id = int(os.environ['GITHUB_REPOSITORY_ID'])
    target = os.environ['GITHUB_REF_NAME']
    head = os.environ['GITHUB_SHA']
    if output('git', 'rev-parse', 'HEAD') != head:
        raise ValueError('checkout differs from the target push')
    tree = output('git', 'rev-parse', 'HEAD^{tree}')
    header = output('git', 'cat-file', 'commit', 'HEAD').split('\n\n', 1)[0]
    parents = [line.removeprefix('parent ') for line in header.splitlines()
               if line.startswith('parent ')]

    def api(endpoint, **parameters):
        return github(repository, endpoint, **parameters)

    seed = find_seed(api, head, tree, target, repository_id, int(os.environ['GITHUB_RUN_ID']), parents)
    if seed is None:
        print('No matching checked branch build for this push.', flush=True)
        return
    run, artifacts = seed
    native_cache = os.environ['LAKE_CACHE_DIR']
    temporary_root = os.environ['RUNNER_TEMP']
    errors = (OSError, ValueError, KeyError, TypeError, zipfile.BadZipFile,
              tarfile.TarError, subprocess.CalledProcessError)
    with tempfile.TemporaryDirectory(prefix='merge-native-', dir=temporary_root) as temporary:
        directory = Path(temporary)
        archive = download(repository, artifacts['cache-staging'], directory, 'lake-native-cache.tar')
        staging = directory / 'stage'
        unpack_native(archive, staging)
        archive.unlink()
        domain = '-'.join((os.environ['RUNNER_OS'], os.environ['RUNNER_ARCH'],
                           sha(Path('lean-toolchain'))[:16]))
        package = tomllib.loads(Path('lakefile.toml').read_text())['name']
        validate_producer(staging, repository, run['head_sha'], package, domain, output('lean', '--version'))
        subprocess.run([sys.executable, '.github/ci-cache/stage.py', 'verify', '--root', '.',
                        '--staging', str(staging), '--native-cache', native_cache], check=True)
        subprocess.run(['lake', 'cache', 'unstage', str(staging), '--force-overwrite'], check=True)
    with open(os.environ['GITHUB_OUTPUT'], 'a') as out:
        out.write('imported=true\n')
    print(f'Imported native merge seed from run {run["id"]} ({run["head_sha"]}).', flush=True)
    for layer, filename in (('dependencies', 'build-dependencies.tar.zst'), ('stacks', 'stacks.tar.zst')):
        artifact = artifacts.get('build-' + layer)
        if artifact is None:
            continue
        try:
            with tempfile.TemporaryDirectory(prefix='merge-checkpoint-', dir=temporary_root) as temporary:
                archive = download(repository, artifact, Path(temporary), filename)
                restore_layer(layer, archive, native_cache)
        except errors as error:
            print(f'::warning::Skipped the branch {layer} checkpoint: {error}', flush=True)


if __name__ == '__main__':
    main()
