/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.Completion
public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.FiltrationFullFaithful

/-! # The actual quotient-row presentation of coarse-weak cofibration chains

The forward functor is the unchanged original initial filtration. Its inverse
adjoins the actual chosen zero and applies the existing exact cofiber functor.
The only extra hypothesis is the structural coarse extension axiom, needed
to recognize every original relative filtration as coarse-weak. Both functors
preserve fine weak maps, and the original quotient maps supply their isos.


Implementation provenance:
`Quillen/Waldhausen/Fibration/RelativeRows/FiltrationEquivalence.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.RelativeRows
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V)

/-- The genuine arrow predicates on the unchanged finite-chain category. -/
def cofibrationWeakChains (n : SimplexCategory) : ObjectProperty (ComposableArrows C n.len) :=
  fun F ↦ (∀ {i j : Fin (n.len + 1)} (f : i ⟶ j), V.cof (F.map f)) ∧
    (∀ {i j : Fin (n.len + 1)} (f : i ⟶ j), N.coarse.weq (F.map f))

/-- This is only the full subcategory of the original finite-chain category. -/
abbrev CofibrationWeakChain (n : SimplexCategory) := (cofibrationWeakChains N n).FullSubcategory

/-- Restrict the unchanged original filtration to its proved arrow predicates. -/
def filtrationPresentation (he : ExtensionAxiom N.coarse) (n : SimplexCategory) :
    Obj N n ⥤ CofibrationWeakChain N n :=
  (cofibrationWeakChains N n).lift (initialFiltrationFunctor N n) (fun F ↦
    ⟨fun f ↦ initialFiltration_map_cof F.obj f, fun f ↦ initialFiltration_map_weak N he F f⟩)

/-- Forgetting the predicates recovers the literal original filtration functor. -/
@[simp] theorem filtrationPresentation_forget (he : ExtensionAxiom N.coarse) (n : SimplexCategory) :
    filtrationPresentation N he n ⋙ (cofibrationWeakChains N n).ι = initialFiltrationFunctor N n
      := rfl

/-- The actual completed map preserves identities. -/
theorem relativeCompletionMap_id {n : SimplexCategory} (F : ComposableArrows C n.len)
    (hF : ∀ {i j : Fin (n.len + 1)} (f : i ⟶ j), V.cof (F.map f))
    (hw : ∀ {i j : Fin (n.len + 1)} (f : i ⟶ j), N.coarse.weq (F.map f)) :
    relativeCompletionMap N hF hw hF hw (𝟙 F) = 𝟙 (relativeCompletion N F hF hw) := by
  apply ObjectProperty.hom_ext
  change QuotientRows.completeCofibrationFlagMap V _ _ ((zeroAugmentFunctor V n.len).map (𝟙 F)) = _
  rw [(zeroAugmentFunctor V n.len).map_id, QuotientRows.completeCofibrationFlagMap_id]
  rfl

/-- The actual completed map preserves composition of all original transformations. -/
theorem relativeCompletionMap_comp {n : SimplexCategory} {F G H : ComposableArrows C n.len}
    (hF : ∀ {i j : Fin (n.len + 1)} (f : i ⟶ j), V.cof (F.map f))
    (hwF : ∀ {i j : Fin (n.len + 1)} (f : i ⟶ j), N.coarse.weq (F.map f))
    (hG : ∀ {i j : Fin (n.len + 1)} (f : i ⟶ j), V.cof (G.map f))
    (hwG : ∀ {i j : Fin (n.len + 1)} (f : i ⟶ j), N.coarse.weq (G.map f))
    (hH : ∀ {i j : Fin (n.len + 1)} (f : i ⟶ j), V.cof (H.map f))
    (hwH : ∀ {i j : Fin (n.len + 1)} (f : i ⟶ j), N.coarse.weq (H.map f))
    (α : F ⟶ G) (β : G ⟶ H) :
    relativeCompletionMap N hF hwF hH hwH (α ≫ β) =
      relativeCompletionMap N hF hwF hG hwG α ≫ relativeCompletionMap N hG hwG hH hwH β := by
  apply ObjectProperty.hom_ext
  change QuotientRows.completeCofibrationFlagMap V _ _ ((zeroAugmentFunctor V n.len).map (α ≫
    β)) = _
  rw [(zeroAugmentFunctor V n.len).map_comp]
  exact QuotientRows.completeCofibrationFlagMap_comp V (zeroAugment_map_cof V F hF)
    (zeroAugment_map_cof V G hG) (zeroAugment_map_cof V H hH)
    ((zeroAugmentFunctor V n.len).map α) ((zeroAugmentFunctor V n.len).map β)

/-- The genuine inverse functor, with the original zero-augmentation/cofiber maps. -/
def completionFunctor (n : SimplexCategory) : CofibrationWeakChain N n ⥤ Obj N n where
  obj F := relativeCompletion N F.obj F.property.1 F.property.2
  map {F G} α := relativeCompletionMap N F.property.1 F.property.2 G.property.1 G.property.2 α.hom
  map_id F := relativeCompletionMap_id N F.obj F.property.1 F.property.2
  map_comp {F G H} α β := relativeCompletionMap_comp N F.property.1 F.property.2
    G.property.1 G.property.2 H.property.1 H.property.2 α.hom β.hom

/-- The inverse map remains literally the previously constructed cofiber completion map. -/
@[simp] theorem completionFunctor_map {n : SimplexCategory} {F G : CofibrationWeakChain N n}
    (α : F ⟶ G) : (completionFunctor N n).map α =
      relativeCompletionMap N F.property.1 F.property.2 G.property.1 G.property.2 α.hom := rfl

/-- Fine weakness in the chain category is the original pointwise fine class. -/
def chainFineWeak (n : SimplexCategory) : MorphismProperty (CofibrationWeakChain N n) :=
  fun _ _ α ↦ ∀ i, V.weq (α.hom.app i)

/-- The forward functor preserves and reflects actual fine weak maps. -/
theorem filtrationPresentation_weak_iff (he : ExtensionAxiom N.coarse) {n : SimplexCategory}
    {F G : Obj N n} (f : F ⟶ G) :
    chainFineWeak N n ((filtrationPresentation N he n).map f) ↔ (waldhausenStructure N n).weq f :=
  (weq_iff_initialFiltrationFunctor N f).symm

/-- Actual cofiber gluing proves that the inverse preserves fine weak maps. -/
theorem completionFunctor_weak {n : SimplexCategory} {F G : CofibrationWeakChain N n}
    (α : F ⟶ G) (hα : chainFineWeak N n α) :
    (waldhausenStructure N n).weq ((completionFunctor N n).map α) :=
  relativeCompletionMap_weak N F.property.1 F.property.2 G.property.1 G.property.2 α.hom hα

/-- On chains, the original quotient-by-zero maps supply the natural isomorphism. -/
def completionFiltrationIso (he : ExtensionAxiom N.coarse) (n : SimplexCategory) :
    𝟭 (CofibrationWeakChain N n) ≅ completionFunctor N n ⋙ filtrationPresentation N he n :=
  NatIso.ofComponents (fun F ↦ (cofibrationWeakChains N n).isoMk
    (relativeCompletionInitialIso N F.obj F.property.1 F.property.2)) (by
      intro F G α
      apply ObjectProperty.hom_ext
      exact relativeCompletionUnit_naturality N F.property.1 F.property.2 G.property.1
        G.property.2 α.hom)

/-- The chain-side comparison retains the original quotient map at every component. -/
@[simp] theorem completionFiltrationIso_hom_app (he : ExtensionAxiom N.coarse) (n : SimplexCategory)
    (F : CofibrationWeakChain N n) (i : Fin (n.len + 1)) :
    ((completionFiltrationIso N he n).hom.app F).hom.app i =
      QuotientRows.completionQuotient V (zeroAugment V F.obj) (zeroAugment_map_cof V F.obj
        F.property.1)
        (interval 0 i.succ (Fin.zero_le _)) := rfl

/-- On actual rows, full faithfulness descends those same original quotient maps. -/
def filtrationCompletionIso (he : ExtensionAxiom N.coarse) (n : SimplexCategory) :
    𝟭 (Obj N n) ≅ filtrationPresentation N he n ⋙ completionFunctor N n :=
  NatIso.ofComponents (fun F ↦ (initialFiltrationFullyFaithful N n).preimageIso
    (relativeCompletionInitialIso N ((filtrationPresentation N he n).obj F).obj
      ((filtrationPresentation N he n).obj F).property.1
      ((filtrationPresentation N he n).obj F).property.2)) (by
    intro F G f
    apply (initialFiltrationFunctor N n).map_injective
    simp only [Functor.map_comp, Functor.FullyFaithful.preimageIso_hom,
      Functor.FullyFaithful.map_preimage]
    exact relativeCompletionUnit_naturality N
      ((filtrationPresentation N he n).obj F).property.1
      ((filtrationPresentation N he n).obj F).property.2
      ((filtrationPresentation N he n).obj G).property.1
      ((filtrationPresentation N he n).obj G).property.2
      ((initialFiltrationFunctor N n).map f))

/-- The genuine categorical presentation equivalence with both original functors. -/
def filtrationEquivalence (he : ExtensionAxiom N.coarse) (n : SimplexCategory) :
    Obj N n ≌ CofibrationWeakChain N n :=
  CategoryTheory.Equivalence.mk (filtrationPresentation N he n) (completionFunctor N n)
    (filtrationCompletionIso N he n) (completionFiltrationIso N he n).symm

@[simp] theorem filtrationEquivalence_functor (he : ExtensionAxiom N.coarse) (n : SimplexCategory) :
    (filtrationEquivalence N he n).functor = filtrationPresentation N he n := rfl

@[simp] theorem filtrationEquivalence_inverse (he : ExtensionAxiom N.coarse) (n : SimplexCategory) :
    (filtrationEquivalence N he n).inverse = completionFunctor N n := rfl

end CategoryTheory.Waldhausen.Fibration.RelativeRows
