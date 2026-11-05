#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

# Maximal Mathlib roots in the pilot's selected import graph.
lake exe cache get \
  Mathlib.Algebra.Category.FGModuleCat.Abelian \
  Mathlib.Algebra.Homology.ShortComplex.ModuleCat \
  Mathlib.LinearAlgebra.FiniteDimensional.Lemmas \
  Mathlib.LinearAlgebra.TensorAlgebra.Grading \
  Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower \
  Mathlib.RingTheory.LocalRing.Length \
  Mathlib.RingTheory.Spectrum.Prime.Noetherian
