/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Comma.Transitions
public import Colib.CategoryTheory.TheoremB.StructuredComparison
public import Colib.CategoryTheory.TheoremA.Conclusion

/-!
# Composition and isomorphisms for actual structured transitions

Adapted from `Quillen/CategoryTheory/TheoremB/StructuredTransitionCalculus.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. These are properties of the
existing native structured-comma precomposition maps.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory
namespace CategoryTheory.TheoremB
variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- A single actual precomposition transition is a homotopy equivalence. -/
def StructuredTransitionIsHE {d e : D} (f : d ⟶ e) : Prop :=
  ∃ E : ContinuousMap.HomotopyEquiv (ClassifyingSpace (StructuredArrow e F))
      (ClassifyingSpace (StructuredArrow d F)), E.toFun = structuredTransitionMap F f

@[simp]
lemma structuredTransitionMap_comp {d e z : D} (f : d ⟶ e) (g : e ⟶ z) :
    structuredTransitionMap F (f ≫ g) =
      (structuredTransitionMap F f).comp (structuredTransitionMap F g) := by
  unfold structuredTransitionMap
  rw [structuredTransition_comp_eq, classifyingSpaceMap_comp, TopCat.hom_comp]

lemma StructuredTransitionIsHE.comp {d e z : D} {f : d ⟶ e} {g : e ⟶ z}
    (hf : StructuredTransitionIsHE F f) (hg : StructuredTransitionIsHE F g) :
    StructuredTransitionIsHE F (f ≫ g) := by
  obtain ⟨E, hE⟩ := hf
  obtain ⟨G, hG⟩ := hg
  refine ⟨G.trans E, ?_⟩
  change E.toFun.comp G.toFun = _
  rw [hE, hG, structuredTransitionMap_comp]

lemma structuredTransitionIsHE_of_isIso {d e : D} (f : d ⟶ e) [IsIso f] :
    StructuredTransitionIsHE F f :=
  ⟨equivalenceClassifyingHomotopyEquiv (StructuredArrow.mapIso (T := F) (asIso f).symm), rfl⟩

/-- Pointwise map-preserving equivalences discharge exactly Theorem B's
structured transition hypothesis. -/
theorem structuredTransitions_of_pointwise
    (h : ∀ ⦃d e : D⦄ (f : d ⟶ e), StructuredTransitionIsHE F f) :
    StructuredTransitionHomotopyEquivalences F := by
  intro d e f
  obtain ⟨E, hE⟩ := h f
  exact ⟨E.invFun, by simpa only [← hE] using E.left_inv,
    by simpa only [← hE] using E.right_inv⟩

end CategoryTheory.TheoremB
