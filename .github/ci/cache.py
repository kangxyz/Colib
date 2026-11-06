#!/usr/bin/env python3
"""Select compact Colib/tool outputs; Mathlib uses its official cache provider."""
import importlib.util
import json
import os
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('checkpoint', ROOT / '.github/ci-cache/checkpoint.py')
checkpoint = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checkpoint)


def own_paths():
    paths = ['.lake/build', '.lake/config', '.lake/tools', '.lake/lint-runner']
    for package, directories in {
        'mathlib': ['bin', 'lib/lean/Cache', 'ir/Cache', 'lib/lean/scripts', 'ir/scripts'],
        'batteries': ['bin', 'lib/lean/scripts', 'ir/scripts'],
    }.items():
        paths.append(f'.lake/packages/{package}/.lake/config')
        paths.extend(f'.lake/packages/{package}/.lake/build/{name}' for name in directories)
    return paths


def main():
    values = checkpoint.contexts(ROOT)
    values['own_paths'] = '\n'.join(own_paths())
    values['own_prefix'] = f'colib-ci-v3-{values["root_context"]}'
    print(json.dumps(values))
    if len(sys.argv) == 2:
        with Path(sys.argv[1]).open('a') as stream:
            for key, value in values.items():
                stream.write(f'{key}<<COLIB_OUTPUT\n{value}\nCOLIB_OUTPUT\n')


if __name__ == '__main__':
    main()
