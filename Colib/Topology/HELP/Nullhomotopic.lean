/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HELP.StrictFiniteCriterion

/-!
# Literal HEP extensions of nullhomotopic boundary maps

A nullhomotopic map on a genuine HEP subspace extends exactly by reversing its
nullhomotopy and extending it from a constant map. Applied to all literal finite
cube boundaries, including the empty zero-cube boundary, this proves complete
weakness of the original map to a point. No global contraction is assumed.

Implementation provenance:
`Quillen/Topology/HELP/Nullhomotopic.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses and universe parameters are retained.
-/
@[expose] public section


noncomputable section
open Topology TopCat
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology

/-- A nullhomotopic map on a genuine HEP subspace extends literally. -/
theorem exists_extend_of_nullhomotopic {A D : TopCat.{u}} {X : Type u}
    [TopologicalSpace X] (i : A ⟶ D) (hi : TopCat.HomotopyExtensionProperty i)
    (a : C(A, X)) (ha : a.Nullhomotopic) :
    ∃ c : C(D, X), c.comp i.hom = a := by
  obtain ⟨x, ⟨H⟩⟩ := ha
  obtain ⟨V, _, hV⟩ := TopCat.homotopyExtensionProperty_continuous hi
    (TopCat.of X) (ContinuousMap.const D x) H.symm.toContinuousMap
    (fun z => H.symm.map_zero_left z)
  refine ⟨⟨fun z => V (1, z), by fun_prop⟩, ?_⟩
  ext z
  exact (hV 1 z).trans (H.symm.map_one_left z)

/-- Nullhomotopies of all genuine finite cube boundaries imply complete
weakness of the actual map to a point, including the empty-boundary test. -/
theorem isWeakHomotopyEquivalence_toPoint_of_boundary_nullhomotopic
    {X : Type u} [TopologicalSpace X]
    (h : ∀ n : ℕ, ∀ a : C(CubicalTests.boundary.{u} n, X), a.Nullhomotopic) :
    IsWeakHomotopyEquivalence (ContinuousMap.const X (PUnit.unit : PUnit.{u + 1})) := by
  apply FiniteCubeStrictHELP.isWeakHomotopyEquivalence
  intro n a b _
  obtain ⟨c, hc⟩ := exists_extend_of_nullhomotopic (CubicalTests.boundaryInclusion n)
    (CubicalTests.boundaryInclusion_hep n) a (h n a)
  refine ⟨c, hc, ?_⟩
  have he : (ContinuousMap.const X (PUnit.unit : PUnit.{u + 1})).comp c = b := by
    ext z
  subst b
  exact ⟨ContinuousMap.HomotopyRel.refl _ _⟩

end Topology
