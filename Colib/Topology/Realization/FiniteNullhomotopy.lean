/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.FiniteSubcomplex
public import Colib.Topology.HELP.Nullhomotopic

/-!
# Weak contractibility from nullhomotopic finite subcomplex inclusions

Exact finite support reduces maps from arbitrary compact spaces to the inclusion
of one finite simplicial subcomplex. Nullhomotopies of these actual inclusions
imply weakness of the original realization-to-point map via whole-boundary HEP.
There is no assumption of a single global contraction or a continuous choice of
finite contractions; the empty-boundary test retains actual nonemptiness.

Implementation provenance:
`Quillen/Topology/Realization/FiniteNullhomotopy.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses and universe parameters are retained.
-/
@[expose] public section


noncomputable section
open Topology TopCat SSet
open CategoryTheory
open scoped Topology Simplicial unitInterval
universe u v
namespace SSet

/-- Exact finite support transports finite-inclusion nullhomotopies to maps
from arbitrary compact spaces. -/
theorem realization_compactMap_nullhomotopic {S : SSet.{u}}
    (h : ∀ A : S.Subcomplex, SSet.Finite A → (SSet.toTop.map A.ι).hom.Nullhomotopic)
    {T : Type v} [TopologicalSpace T] [CompactSpace T] (f : C(T, |S|)) :
    f.Nullhomotopic := by
  obtain ⟨A, hA, g, hg⟩ := realization_continuousMap_factors_finiteSubcomplex f
  rw [← hg]
  exact (h A hA).comp_left g

/-- Contracting each finite subcomplex inclusion inside the whole realization
proves weakness of its actual map to a point. A global contraction is not assumed. -/
theorem realization_toPoint_isWeakHomotopyEquivalence_of_finite_nullhomotopic
    {S : SSet.{u}}
    (h : ∀ A : S.Subcomplex, SSet.Finite A → (SSet.toTop.map A.ι).hom.Nullhomotopic) :
    IsWeakHomotopyEquivalence (ContinuousMap.const |S| (PUnit.unit : PUnit.{u + 1})) := by
  apply isWeakHomotopyEquivalence_toPoint_of_boundary_nullhomotopic
  intro n a
  let : CompactSpace (CubicalTests.boundaryPresentation.{u} n).space :=
    (CubicalTests.boundaryPresentation n).compact
  let : CompactSpace (CubicalTests.boundary.{u} n) :=
    (CubicalTests.boundaryPresentationHomeomorph n).compactSpace
  exact realization_compactMap_nullhomotopic h a

end SSet
