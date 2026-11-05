# Colib

Colib formalizes cohomology and homotopy theory in algebraic geometry, including their
motivic and algebraic K-theoretic interfaces. Its mathematical dependencies are Mathlib and
[AxiomMath/Stacks](https://github.com/AxiomMath/Stacks), pinned to exact commits.

The [online encyclopedia](https://kangxyz.github.io/colib/) provides permanent result links,
reference search, scope notes and the actual Lean signatures.

## Initial pilot

The first release develops three closed mathematical slices.

- The dimension equivalence from the Grothendieck group of finite-dimensional vector spaces
  to the integers, normalized on object classes.
- The comparison of the ordered-pair Steinberg tensor quotient with the canonical Stacks
  degree-two Milnor group, preserving each tensor class.
- The dimension formula for a finite algebra over a field as the sum of local lengths
  weighted by residue-field degrees.

The [encyclopedia](docs/ENCYCLOPEDIA.md) describes the twelve permanent entries and their
reference and review conventions. CI exports the actual Lean signatures and defining modules
as the artifact `colib-encyclopedia`. Release catalog assets are versioned with the code.

## Use and build

The pinned toolchain is Lean 4.34.0-rc2. Add the repository as a Lake dependency
using a Git checkout and an exact release commit.

```lean
import Colib
```

Focused imports are available at
`Colib.KTheory.GrothendieckGroup.Field`,
`Colib.KTheory.MilnorK.DegreeTwo`, and
`Colib.AlgebraicGeometry.Cycles.FiniteAlgebra`.

```sh
bash scripts/cache.sh
lake build Colib
lake test
bash scripts/check.sh
```

The [development guide](docs/DEVELOPMENT.md) owns checks and caches.
The [architecture](docs/ARCHITECTURE.md) owns mathematical organization.
The [migration plan](docs/MIGRATION.md) records subsequent Quillen and Motivic work.
The catalog's `author_checked` state records the author's source comparison.

## License

[Apache-2.0](LICENSE).
