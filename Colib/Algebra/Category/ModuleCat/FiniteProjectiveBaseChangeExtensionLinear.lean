/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeExtension
public import Colib.CategoryTheory.GroupCompletion.MonoidalFunctor

/-!
# Genuine direct-sum linearity of original extension base change

## Implementation provenance

Adapted from `Quillen/Algebra/Category/ModuleCat/FiniteProjectiveBaseChangeExtensionLinear.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, chosen paths, and original
proof hypotheses are retained under native ownership.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalLeftAction
namespace ModuleCat.FiniteProjective
attribute [local instance] categoryDirectSumMonoidal categoryDirectSumSymmetric
  directSumMonoidal directSumSymmetric inflationDirectSumAction
  rightBaseChangeMonoidal rightBaseChangeCoreMonoidal
variable {R S : Type u} [Ring R] [Ring S] (f : R →+* S)

private theorem extension_actionLeft_domain {P Q : IsoCategory Rᵐᵒᵖ} (a : P ⟶ Q)
    (x : (exactStructure Rᵐᵒᵖ).ExtensionTotal) :
    (Subdivision.domainMap (a ⊵ₗ x)).hom = a.iso.inv ▷ x.fiber.unop.left.obj := by
  change (inv a ⊙ₗₘ Subdivision.domainMap (𝟙 x)).hom = _
  simp only [Subdivision.domainMap_id, MonoidalLeftAction.actionHom_id,
    ← Groupoid.inv_eq_inv]
  rfl

private theorem extension_actionRight_domain (P : IsoCategory Rᵐᵒᵖ)
    {x y : (exactStructure Rᵐᵒᵖ).ExtensionTotal} (a : x ⟶ y) :
    (Subdivision.domainMap (P ⊴ₗ a)).hom = P.of ◁ (Subdivision.domainMap a).hom := by
  change (inv (𝟙 P) ⊙ₗₘ Subdivision.domainMap a).hom = _
  simp only [IsIso.inv_id, MonoidalLeftAction.id_actionHom]
  rfl

private theorem extension_actionLeft_middle {P Q : IsoCategory Rᵐᵒᵖ} (a : P ⟶ Q)
    (x : (exactStructure Rᵐᵒᵖ).ExtensionTotal) :
    (a ⊵ₗ x).base.hom = a.iso.hom ▷ x.base.obj := by
  change (a ⊙ₗₘ 𝟙 x.base).hom = _
  rw [MonoidalLeftAction.actionHom_id]
  rfl

private theorem extension_actionRight_middle (P : IsoCategory Rᵐᵒᵖ)
    {x y : (exactStructure Rᵐᵒᵖ).ExtensionTotal} (a : x ⟶ y) :
    (P ⊴ₗ a).base.hom = P.of ◁ a.base.hom := by
  change ((𝟙 P) ⊙ₗₘ a.base).hom = _
  rw [MonoidalLeftAction.id_actionHom]
  rfl

private theorem extension_associator_domain (P Q : IsoCategory Rᵐᵒᵖ)
    (x : (exactStructure Rᵐᵒᵖ).ExtensionTotal) :
    (Subdivision.domainMap (αₗ P Q x).hom).hom =
      (α_ P.of Q.of x.fiber.unop.left.obj).inv := rfl

private theorem extension_associator_middle (P Q : IsoCategory Rᵐᵒᵖ)
    (x : (exactStructure Rᵐᵒᵖ).ExtensionTotal) :
    (αₗ P Q x).hom.base.hom = (α_ P.of Q.of x.base.obj).hom := rfl

private theorem extension_unitor_middle (x : (exactStructure Rᵐᵒᵖ).ExtensionTotal) :
    (λₗ[IsoCategory Rᵐᵒᵖ] x).hom.base.hom = (λ_ x.base.obj).hom := rfl

private theorem baseChange_extension_domain {x y : (exactStructure Rᵐᵒᵖ).ExtensionTotal}
    (a : x ⟶ y) :
    (Subdivision.domainMap ((rightBaseChangeExtension f).map a)).hom =
      (rightBaseChange f).map (Subdivision.domainMap a).hom := rfl

private theorem baseChange_extension_middle {x y : (exactStructure Rᵐᵒᵖ).ExtensionTotal}
    (a : x ⟶ y) :
    ((rightBaseChangeExtension f).map a).base.hom =
      (rightBaseChange f).map a.base.hom := rfl

/-- Naturality in the original projective actor, retaining the reversed kernel map. -/
theorem rightBaseChangeExtensionTensorIso_naturality_left
    {P Q : IsoCategory Rᵐᵒᵖ} (a : P ⟶ Q) (x : (exactStructure Rᵐᵒᵖ).ExtensionTotal) :
    (rightBaseChangeCore f).map a ⊵ₗ (rightBaseChangeExtension f).obj x ≫
        (rightBaseChangeExtensionTensorIso f Q x).hom =
      (rightBaseChangeExtensionTensorIso f P x).hom ≫
        (rightBaseChangeExtension f).map (a ⊵ₗ x) := by
  apply Subdivision.hom_ext
  · simp only [Subdivision.domainMap_comp]
    apply WideSubcategory.hom_ext
    simp only [WideSubcategory.comp_def, rightBaseChangeExtensionTensorIso_domain,
      extension_actionLeft_domain]
    change _ = (rightBaseChange f).map (Subdivision.domainMap (a ⊵ₗ x)).hom ≫ _
    rw [extension_actionLeft_domain]
    exact Functor.OplaxMonoidal.δ_natural_left (rightBaseChange f) a.iso.inv _
  · simp only [Grothendieck.comp_base]
    apply WideSubcategory.hom_ext
    simp only [WideSubcategory.comp_def, rightBaseChangeExtensionTensorIso_middle]
    change ((rightBaseChangeCore f).map a ⊙ₗₘ
      𝟙 ((rightBaseChangeExact f).inflationFunctor.obj x.base)).hom ≫ _ =
      _ ≫ (rightBaseChange f).map (a ⊙ₗₘ 𝟙 x.base).hom
    simp only [MonoidalLeftAction.actionHom_id]
    exact Functor.LaxMonoidal.μ_natural_left (rightBaseChange f) a.iso.hom x.base.obj

/-- Naturality in every actual extension arrow, whose kernel map need not be invertible. -/
theorem rightBaseChangeExtensionTensorIso_naturality_right
    (P : IsoCategory Rᵐᵒᵖ) {x y : (exactStructure Rᵐᵒᵖ).ExtensionTotal} (a : x ⟶ y) :
    (rightBaseChangeCore f).obj P ⊴ₗ (rightBaseChangeExtension f).map a ≫
        (rightBaseChangeExtensionTensorIso f P y).hom =
      (rightBaseChangeExtensionTensorIso f P x).hom ≫
        (rightBaseChangeExtension f).map (P ⊴ₗ a) := by
  apply Subdivision.hom_ext
  · simp only [Subdivision.domainMap_comp]
    apply WideSubcategory.hom_ext
    simp only [WideSubcategory.comp_def, rightBaseChangeExtensionTensorIso_domain,
      extension_actionRight_domain]
    change _ = (rightBaseChange f).map (Subdivision.domainMap (P ⊴ₗ a)).hom ≫ _
    rw [extension_actionRight_domain]
    exact Functor.OplaxMonoidal.δ_natural_right (rightBaseChange f) P.of
      (Subdivision.domainMap a).hom
  · simp only [Grothendieck.comp_base]
    apply WideSubcategory.hom_ext
    simp only [WideSubcategory.comp_def, rightBaseChangeExtensionTensorIso_middle]
    change ((𝟙 ((rightBaseChangeCore f).obj P)) ⊙ₗₘ
      (rightBaseChangeExact f).inflationFunctor.map a.base).hom ≫ _ =
      _ ≫ (rightBaseChange f).map ((𝟙 P) ⊙ₗₘ a.base).hom
    simp only [MonoidalLeftAction.id_actionHom]
    exact Functor.LaxMonoidal.μ_natural_right (rightBaseChange f) P.of a.base.hom

private lemma inverse_congr {A B : Category.{u, u} Sᵐᵒᵖ}
    (a b : A ⟶ B) [IsIso a] [IsIso b] (h : a = b) : inv a = inv b := by
  subst b
  rfl

private theorem tensorator_inverse_associativity
    (P Q X : Category.{u, u} Rᵐᵒᵖ) :
    (rightBaseChange f).map (α_ P Q X).inv ≫
      Functor.OplaxMonoidal.δ (rightBaseChange f) (P ⊗ Q) X =
    Functor.OplaxMonoidal.δ (rightBaseChange f) P (Q ⊗ X) ≫
      (rightBaseChange f).obj P ◁ Functor.OplaxMonoidal.δ (rightBaseChange f) Q X ≫
      (α_ ((rightBaseChange f).obj P) ((rightBaseChange f).obj Q)
        ((rightBaseChange f).obj X)).inv ≫
      Functor.LaxMonoidal.μ (rightBaseChange f) P Q ▷ (rightBaseChange f).obj X := by
  have h := inverse_congr _ _
    (GroupCompletion.monoidalFunctor_action_associativity (rightBaseChange f) P Q X)
  simpa only [IsIso.inv_comp, ← Functor.map_inv, IsIso.Iso.inv_hom,
    MonoidalCategory.inv_whiskerLeft, MonoidalCategory.inv_whiskerRight,
    Functor.Monoidal.μIso_inv, Functor.Monoidal.inv_μ, Functor.Monoidal.inv_δ,
    Category.assoc] using h

private theorem tensorator_inverse_unitality (X : Category.{u, u} Rᵐᵒᵖ) :
    (λ_ ((rightBaseChange f).obj X)).inv ≫
      Functor.LaxMonoidal.ε (rightBaseChange f) ▷ (rightBaseChange f).obj X =
    (rightBaseChange f).map (λ_ X).inv ≫
      Functor.OplaxMonoidal.δ (rightBaseChange f) (𝟙_ _) X := by
  have h := inverse_congr _ _
    (GroupCompletion.monoidalFunctor_action_unitality (rightBaseChange f) X)
  simpa only [IsIso.inv_comp, ← Functor.map_inv, IsIso.Iso.inv_hom,
    MonoidalCategory.inv_whiskerRight, Functor.Monoidal.εIso_inv,
    Functor.Monoidal.inv_η, Functor.Monoidal.inv_μ] using h

private theorem core_tensor_iso (P Q : IsoCategory Rᵐᵒᵖ) :
    Functor.Monoidal.μIso (rightBaseChangeCore f) P Q =
      Core.isoMk (rightBaseChangeTensorIso f P.of Q.of) := by
  apply Iso.ext
  rfl

/-- The original tensorator defines actual linearity for the explicitly restricted target action. -/
@[instance_reducible]
def rightBaseChangeExtensionLinear :
    letI := MonoidalLeftAction.restrictAlong
      (D := (exactStructure Sᵐᵒᵖ).ExtensionTotal) (rightBaseChangeCore f)
    (rightBaseChangeExtension f).LaxLeftLinear (IsoCategory Rᵐᵒᵖ) := by
  letI := MonoidalLeftAction.restrictAlong
    (D := (exactStructure Sᵐᵒᵖ).ExtensionTotal) (rightBaseChangeCore f)
  exact {
    μₗ := fun P x ↦ (rightBaseChangeExtensionTensorIso f P x).hom
    μₗ_naturality_left := fun a x ↦ rightBaseChangeExtensionTensorIso_naturality_left f a x
    μₗ_naturality_right := fun P _ _ a ↦
      rightBaseChangeExtensionTensorIso_naturality_right f P a
    μₗ_associativity := by
      intro P Q x
      rw [MonoidalLeftAction.restrictAlong_associator]
      apply Subdivision.hom_ext
      · simp only [Subdivision.domainMap_comp]
        apply WideSubcategory.hom_ext
        simp only [WideSubcategory.comp_def, rightBaseChangeExtensionTensorIso_domain,
          extension_actionLeft_domain, baseChange_extension_domain,
          extension_associator_domain]
        change _ = (_ ≫ (Subdivision.domainMap
          ((rightBaseChangeCore f).obj P ⊴ₗ (rightBaseChangeExtensionTensorIso f Q x).hom)).hom) ≫ _
        rw [extension_actionRight_domain, rightBaseChangeExtensionTensorIso_domain]
        rw [core_tensor_iso]
        have h := tensorator_inverse_associativity f P.of Q.of x.fiber.unop.left.obj
        simp only [Category.assoc] at h ⊢
        exact h
      · simp only [Grothendieck.comp_base]
        apply WideSubcategory.hom_ext
        simp only [WideSubcategory.comp_def, rightBaseChangeExtensionTensorIso_middle,
          baseChange_extension_middle, extension_associator_middle,
          extension_actionLeft_middle]
        change _ = _ ≫ _ ≫
          (((rightBaseChangeCore f).obj P) ⊴ₗ
            (rightBaseChangeExtensionTensorIso f Q x).hom).base.hom ≫ _
        rw [extension_actionRight_middle, rightBaseChangeExtensionTensorIso_middle]
        rw [core_tensor_iso]
        have h := GroupCompletion.monoidalFunctor_action_associativity
          (rightBaseChange f) P.of Q.of x.base.obj
        exact h
    μₗ_unitality := by
      intro x
      rw [MonoidalLeftAction.restrictAlong_unitor]
      apply Subdivision.hom_ext
      · simp only [Subdivision.domainMap_comp]
        apply WideSubcategory.hom_ext
        simp only [WideSubcategory.comp_def, rightBaseChangeExtensionTensorIso_domain,
          extension_actionLeft_domain]
        exact tensorator_inverse_unitality f x.fiber.unop.left.obj
      · simp only [Grothendieck.comp_base]
        apply WideSubcategory.hom_ext
        simp only [WideSubcategory.comp_def, rightBaseChangeExtensionTensorIso_middle,
          baseChange_extension_middle, extension_unitor_middle, extension_actionLeft_middle]
        exact GroupCompletion.monoidalFunctor_action_unitality (rightBaseChange f) x.base.obj }

end ModuleCat.FiniteProjective
