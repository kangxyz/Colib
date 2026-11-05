# Independent Stacks dependency artifacts

Colib keeps three artifact sources with separate identities.

| Layer | Identity and storage |
| --- | --- |
| Mathlib | Its exact manifest pin and official module cache, acquired by scripts/cache.sh |
| Stacks | A dedicated Actions cache for .lake/packages/Stacks, with an exact pinned dependency/toolchain/platform context |
| Colib and other environment outputs | Explicit root/configuration/tool paths and the non-Stacks packages, selected by scripts/stacks_cache.py layout |

The common Actions cache includes neither the Stacks package directory nor the mixed native
content store. The native store remains a build-local working directory. Colib's checked
native mappings are staged and published through the existing native cache release path.

Stacks also has an independent artifact-only archive. It contains its selected .lake/build
files and metadata with the Stacks revision, all resolved dependency pins, toolchain, platform
and per-file digests. Successful native CI publishes this archive under a separate
`stacks-native-…` release tag. The archive contains the compiled import closure selected by
Colib at that producer revision.

## Export and import

After a selected native build has completed, export its Stacks artifacts.

```sh
python3 scripts/stacks_cache.py pack build/stacks-native-cache.tar.gz
```

Restore a downloaded matching archive through the dependency boundary.

```sh
python3 scripts/stacks_cache.py restore build/stacks-native-cache.tar.gz
lake build --rehash Colib
```

Import validates the complete identity and archive before installing files under the Stacks
build directory. It rejects mismatched pins, platforms, unsafe paths and damaged artifacts.
The ordinary native build decides artifact applicability against the actual sources and options.
Archive restoration retains its producer identity and selected scope.

## Future upstream service

An upstream Stacks cache can be acquired at the existing Stacks restore step and installed in
its own dependency build directory. Its adapter will follow the upstream service's actual
format and compatibility contract. Mathlib acquisition, Colib caches and the native
build/test/lint/axiom checks use their existing boundaries.

The initial Actions cache also retains the Stacks source checkout for efficient cold-run
preparation. The separately published archive contains build artifacts only.
