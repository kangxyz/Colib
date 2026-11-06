/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HELP.FiniteCharacterization
public import Colib.Topology.HELP.StrictPair

/-!
# Weak equivalences characterized by strict finite cube HELP

Only literal finite cube-boundary pairs are tested. An actual strict square
has a lift up to homotopy fixed on its whole original boundary. The proved
HEP correction for that same pair recovers every prescribed boundary path,
so the existing finite full-HELP criterion applies. Dimension zero remains
part of the condition; no nonempty-source or compact-pair assumption is added.


Implementation provenance:
`Quillen/Topology/HELP/StrictFiniteCriterion.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Strict-square HELP on every literal finite cube, with the entire original
boundary fixed. The zero-cube has its genuine empty boundary. -/
def FiniteCubeStrictHELP (f : C(X, Y)) : Prop :=
  ∀ (n : ℕ) (a : C(CubicalTests.boundary.{u} n,X)) (b : C(CubicalTests.cube.{u} n,Y)),
    f.comp a = b.comp (CubicalTests.boundaryInclusion n).hom →
      ∃ c : C(CubicalTests.cube.{u} n,X),
        c.comp (CubicalTests.boundaryInclusion n).hom = a ∧
          Nonempty ((f.comp c).HomotopyRel b (Set.range (CubicalTests.boundaryInclusion n)))

/-- HEP for the actual cube boundary converts strict finite HELP into full
finite HELP while preserving each prescribed boundary path exactly. -/
theorem FiniteCubeStrictHELP.full {f : C(X, Y)} (hf : FiniteCubeStrictHELP f) :
    FiniteCubeHELP f := by
  intro n a b H
  exact fullHELP_at_pair_of_strict f _ _ (CubicalTests.boundaryInclusion n)
    (CubicalTests.boundaryInclusion_hep n) (hf n) a b H

/-- The strict finite test implies complete weakness of the original map,
including component surjectivity and the ungrouped zero-dimensional test. -/
theorem FiniteCubeStrictHELP.isWeakHomotopyEquivalence {f : C(X, Y)}
    (hf : FiniteCubeStrictHELP f) : IsWeakHomotopyEquivalence f :=
  (isWeakHomotopyEquivalence_iff_finiteCubeHELP f).mpr hf.full

/-- Exact strict-cube characterization of the empty-aware weak property.
It asserts neither arbitrary compact HELP nor a continuous homotopy inverse. -/
theorem isWeakHomotopyEquivalence_iff_finiteCubeStrictHELP (f : C(X, Y)) :
    IsWeakHomotopyEquivalence f ↔ FiniteCubeStrictHELP f :=
  ⟨fun hf ↦ hf.cube_strictHELP, fun hf ↦ hf.isWeakHomotopyEquivalence⟩

end Topology
