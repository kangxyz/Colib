/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.RankedChain.Resolution
public import Colib.Topology.Realization.FinitePosetSupport
public import Colib.Topology.HELP.Nullhomotopic

/-!
# Weak contractibility from actual finite-poset diagrams

Every small category has a genuine poset resolution whose original map is an
actual homotopy equivalence. Exact compact support in finite full subposets
therefore transports nullhomotopies of actual finite-poset diagram maps to
all compact-source maps. Literal cube-boundary tests give complete weakness
of the original map to a point, including nonemptiness and degree zero.
There is no finite triangulation or weak-to-homotopy-equivalence assumption.

Implementation provenance:
`Quillen/Topology/ClassifyingSpace/FinitePosetCriterion.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses and universe parameters are retained.
-/
@[expose] public section


noncomputable section
open Topology TopCat SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology
universe u v
namespace CategoryTheory

/-- Actual finite-poset diagram nullhomotopies contract every compact map into
an arbitrary category nerve, using its genuine poset resolution. -/
theorem classifyingSpace_compactMap_nullhomotopic_of_finitePoset
    {C : Type u} [SmallCategory C]
    (h : ∀ (J : Type u) [PartialOrder J] [Finite J] (K : J ⥤ C),
      (classifyingSpaceMap K).hom.Nullhomotopic)
    {T : Type v} [TopologicalSpace T] [CompactSpace T]
    (f : C(T, ClassifyingSpace C)) : f.Nullhomotopic := by
  let e := RankedChainOrder.resolutionHomotopyEquiv C
  obtain ⟨s, hs, g, hg⟩ := FiniteNervePosetSupport.compactMap_factors (e.invFun.comp f)
  let : Finite s := hs.to_subtype
  have hn := (h s (FiniteNervePosetSupport.inclusion s ⋙
    RankedChainOrder.resolutionFunctor C)).comp_left g
  have he : (classifyingSpaceMap (FiniteNervePosetSupport.inclusion s ⋙
      RankedChainOrder.resolutionFunctor C)).hom.comp g =
      e.toFun.comp (e.invFun.comp f) := by
    rw [classifyingSpaceMap_comp]
    change (classifyingSpaceMap (RankedChainOrder.resolutionFunctor C)).hom.comp
      ((classifyingSpaceMap (FiniteNervePosetSupport.inclusion s)).hom.comp g) = _
    rw [hg]
    simp only [e, RankedChainOrder.resolutionHomotopyEquiv_toFun]
  rw [he] at hn
  obtain ⟨c, hc⟩ := hn
  refine ⟨c, ?_⟩
  exact ((e.right_inv.comp (ContinuousMap.Homotopic.refl f))).symm.trans hc

/-- Nullhomotopies of all original finite-poset diagrams imply complete weakness
of the original map to a point, including the empty-boundary test. -/
theorem classifyingSpace_toPoint_isWeakHomotopyEquivalence_of_finitePoset
    {C : Type u} [SmallCategory C]
    (h : ∀ (J : Type u) [PartialOrder J] [Finite J] (K : J ⥤ C),
      (classifyingSpaceMap K).hom.Nullhomotopic) :
    IsWeakHomotopyEquivalence
      (ContinuousMap.const (ClassifyingSpace C) (PUnit.unit : PUnit.{u + 1})) := by
  apply isWeakHomotopyEquivalence_toPoint_of_boundary_nullhomotopic
  intro n a
  let : CompactSpace (CubicalTests.boundaryPresentation.{u} n).space :=
    (CubicalTests.boundaryPresentation n).compact
  let : CompactSpace (CubicalTests.boundary.{u} n) :=
    (CubicalTests.boundaryPresentationHomeomorph n).compactSpace
  exact classifyingSpace_compactMap_nullhomotopic_of_finitePoset h a

end CategoryTheory
