/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.Topology.ClassifyingSpace.GroupoidCompletion

/-!
# Naturality of realization into categorical groupoid completion

Extracted from the first six declarations of
`Quillen/Topology/ClassifyingSpace/CompletionRetraction.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The actual localization nerve map, realized map, vertex and edge formulas,
independent object and morphism universes, and natural isomorphisms are retained.
The completion-level isomorphism uses Mathlib's `Localization.liftNatIso`.
Only namespace and import ownership change. No retraction, injectivity or
fundamental-group equivalence is asserted in this module.
-/
@[expose] public section

noncomputable section
universe u v
open CategoryTheory Opposite SSet
open scoped Simplicial Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory
variable (C : Type u) [Category.{v} C]

/-- The nerve map of the genuine groupoid-localization functor, expressed by
postcomposition so that independent category universes are preserved. -/
def groupoidCompletionNerveMap :
    nerve C ⟶ nerve (⊤ : MorphismProperty C).Localization where
  app _ := ↾fun F ↦ F ⋙ (⊤ : MorphismProperty C).Q
  naturality _ _ _ := by ext F; rfl

/-- Realization of the genuine localization functor. -/
def classifyingSpaceCompletionMap :
    ClassifyingSpace C ⟶ ClassifyingSpace (⊤ : MorphismProperty C).Localization :=
  SSet.toTop.map (groupoidCompletionNerveMap C)

@[simp] theorem classifyingSpaceCompletionMap_point (c : C) :
    classifyingSpaceCompletionMap C (classifyingSpacePoint c) =
      classifyingSpacePoint ((⊤ : MorphismProperty C).Q.obj c) := by
  change SSet.toTop.map (groupoidCompletionNerveMap C) (realizationPoint (nerveVertex c)) = _
  rw [realizationPoint_naturality]
  exact congrArg realizationPoint (ComposableArrows.ext₀ rfl)

/-- The localization nerve map preserves each original realized edge exactly. -/
theorem classifyingSpaceCompletionMap_path {c d : C} (f : c ⟶ d) :
    ((classifyingSpacePath f).map (classifyingSpaceCompletionMap C).hom.continuous).cast
      (classifyingSpaceCompletionMap_point C c).symm
      (classifyingSpaceCompletionMap_point C d).symm =
      classifyingSpacePath ((⊤ : MorphismProperty C).Q.map f) := by
  ext t
  change SSet.toTop.map (groupoidCompletionNerveMap C) (classifyingSpacePath f t) = _
  have he : (groupoidCompletionNerveMap C).app (op ⦋1⦌) (ComposableArrows.mk₁ f) =
      ComposableArrows.mk₁ ((⊤ : MorphismProperty C).Q.map f) :=
    ComposableArrows.ext₁ rfl rfl (by simp [groupoidCompletionNerveMap])
  exact (realizationEdgePath_naturality_apply (groupoidCompletionNerveMap C)
    (CategoryTheory.nerve.edgeMk f) t).trans
      (congrArg (fun e : (nerve (⊤ : MorphismProperty C).Localization) _⦋1⦌ ↦
        SSet.toTop.map (SSet.yonedaEquiv.symm e) (realizationInterval t)) he)

/-- Realized original arrows commute with the map into the completion's
classifying space, with the actual vertex equalities as components. -/
def classifyingFundamentalGroupoidCompletionNaturality :
    classifyingFundamentalGroupoidFunctor C ⋙
        FundamentalGroupoid.map (classifyingSpaceCompletionMap C).hom ≅
      (⊤ : MorphismProperty C).Q ⋙
        classifyingFundamentalGroupoidFunctor (⊤ : MorphismProperty C).Localization :=
  NatIso.ofComponents (fun c ↦ eqToIso (congrArg FundamentalGroupoid.mk
    (classifyingSpaceCompletionMap_point C c))) (by
    intro c d f
    apply (cancel_epi (eqToHom (congrArg FundamentalGroupoid.mk
      (classifyingSpaceCompletionMap_point C c).symm))).1
    simp only [eqToIso, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
    rw [Category.assoc]
    change eqToHom (congrArg FundamentalGroupoid.mk
        (classifyingSpaceCompletionMap_point C c).symm) ≫
      (⟦(classifyingSpacePath f).map (classifyingSpaceCompletionMap C).hom.continuous⟧ :
        Path.Homotopic.Quotient _ _) ≫
      eqToHom (congrArg FundamentalGroupoid.mk (classifyingSpaceCompletionMap_point C d)) = _
    rw [FundamentalGroupoid.conj_eqToHom
      (classifyingSpaceCompletionMap_point C c).symm
      (classifyingSpaceCompletionMap_point C d).symm]
    exact congrArg Path.Homotopic.Quotient.mk (classifyingSpaceCompletionMap_path C f))

/-- Extend the original-arrow naturality square over the genuine groupoid
completion by its localization universal property. -/
def classifyingGroupoidCompletionNaturality :
    classifyingGroupoidCompletionFunctor C ⋙
        FundamentalGroupoid.map (classifyingSpaceCompletionMap C).hom ≅
      classifyingFundamentalGroupoidFunctor (⊤ : MorphismProperty C).Localization := by
  let A := classifyingGroupoidCompletionFunctor C ⋙
    FundamentalGroupoid.map (classifyingSpaceCompletionMap C).hom
  let B := classifyingFundamentalGroupoidFunctor (⊤ : MorphismProperty C).Localization
  let Q := (⊤ : MorphismProperty C).Q
  apply Localization.liftNatIso Q ⊤ (Q ⋙ A) (Q ⋙ B) A B
  exact (eqToIso (by
    dsimp only [Q, A]
    rw [← Functor.assoc, toClassifyingGroupoidCompletionFunctor])) ≪≫
      classifyingFundamentalGroupoidCompletionNaturality C

end CategoryTheory

attribute [colib_tag "COL-0093",
  colib_ref "WeibelKBook" "IV, Characterization 3.1(1) and Definition 3.1.4, pages 24-25"
    "background"
    "Functorial nerve realization and completion naturality, not a retraction"]
  CategoryTheory.groupoidCompletionNerveMap
  CategoryTheory.classifyingSpaceCompletionMap
  CategoryTheory.classifyingSpaceCompletionMap_point
  CategoryTheory.classifyingSpaceCompletionMap_path
  CategoryTheory.classifyingFundamentalGroupoidCompletionNaturality
  CategoryTheory.classifyingGroupoidCompletionNaturality
