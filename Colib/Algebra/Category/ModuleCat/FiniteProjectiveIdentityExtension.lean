/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionEquivariance
public import Colib.CategoryTheory.ExactCategory.ExtensionIdentityFunctor
public import Mathlib.CategoryTheory.Monoidal.Action.LinearFunctor

/-!
Implementation provenance:
`Quillen/Algebra/Category/ModuleCat/FiniteProjectiveIdentityExtension.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Direct-sum linearity of the actual identity-extension functor -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal inflationDirectSumAction
  extensionDirectSumAction

/-- The identity endpoint maps compare a translated identity extension with
the identity extension of the translated module. -/
def identityExtensionLineator (S A : IsoCategory R) :
    S ⊙ₗ (exactStructure R).identityExtensionFunctor.obj A ⟶
      (exactStructure R).identityExtensionFunctor.obj (S ⊗ A) :=
  Subdivision.homMk (𝟙 _) (𝟙 _) (by
    apply WideSubcategory.hom_ext
    change 𝟙 _ ≫ S.of ◁ 𝟙 A.of ≫ 𝟙 _ = 𝟙 _
    simp)

/-- The lineator is an actual isomorphism, with identity endpoint maps. -/
def identityExtensionLineatorIso (S A : IsoCategory R) :
    S ⊙ₗ (exactStructure R).identityExtensionFunctor.obj A ≅
      (exactStructure R).identityExtensionFunctor.obj (S ⊗ A) :=
  Subdivision.isoMk (Iso.refl _) (Iso.refl _) (by
    apply WideSubcategory.hom_ext
    change S.of ◁ 𝟙 A.of ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
    simp)

instance identityExtensionLineator_isIso (S A : IsoCategory R) :
    IsIso (identityExtensionLineator R S A) :=
  inferInstanceAs (IsIso (identityExtensionLineatorIso R S A).hom)

/-- Identity extensions respect direct sums with the original coherent action. -/
@[instance_reducible]
def identityExtensionLinear :
    (exactStructure R).identityExtensionFunctor.LaxLeftLinear (IsoCategory R) where
  μₗ := identityExtensionLineator R
  μₗ_naturality_left f A := by
    apply Subdivision.hom_ext
    · simp only [Subdivision.domainMap_comp]
      apply WideSubcategory.hom_ext
      change 𝟙 _ ≫ ((inv f).iso.hom ▷ A.of ≫ _ ◁ 𝟙 _) = (f ▷ A).iso.inv ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id, whiskerLeft_id]
      rw [← Groupoid.inv_eq_inv]
      rfl
    · apply WideSubcategory.hom_ext
      change (f.iso.hom ▷ A.of ≫ _ ◁ 𝟙 _) ≫ 𝟙 _ = 𝟙 _ ≫ (f ▷ A).iso.hom
      simp only [Category.id_comp, Category.comp_id, whiskerLeft_id]
      rfl
  μₗ_naturality_right S _ _ f := by
    apply Subdivision.hom_ext
    · simp only [Subdivision.domainMap_comp]
      apply WideSubcategory.hom_ext
      change 𝟙 _ ≫ ((inv (𝟙 S)).iso.hom ▷ _ ≫ S.of ◁ f.iso.inv) = (S ◁ f).iso.inv ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id, IsIso.inv_id,
        coreCategory_id_iso, Iso.refl_hom, id_whiskerRight]
      rfl
    · apply WideSubcategory.hom_ext
      change ((𝟙 _ ▷ _) ≫ S.of ◁ f.iso.hom) ≫ 𝟙 _ = 𝟙 _ ≫ (S ◁ f).iso.hom
      simp only [Category.id_comp, Category.comp_id, id_whiskerRight]
      rfl
  μₗ_associativity S T A := by
    apply Subdivision.hom_ext
    · simp only [Subdivision.domainMap_comp]
      apply WideSubcategory.hom_ext
      change (α_ S T A).hom.iso.inv ≫ 𝟙 _ =
        (𝟙 _ ≫ ((inv (𝟙 S)).iso.hom ▷ _ ≫ S.of ◁ 𝟙 _)) ≫
          (α_ S.of T.of A.of).inv
      simp only [Category.id_comp, Category.comp_id, whiskerLeft_id, IsIso.inv_id,
        coreCategory_id_iso, Iso.refl_hom, id_whiskerRight]
      rfl
    · apply WideSubcategory.hom_ext
      change 𝟙 _ ≫ (α_ S T A).hom.iso.hom =
        (α_ S.of T.of A.of).hom ≫ ((𝟙 _ ▷ _) ≫ S.of ◁ 𝟙 _) ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id, whiskerLeft_id, id_whiskerRight]
      rfl
  μₗ_unitality A := by
    apply Subdivision.hom_ext
    · simp only [Subdivision.domainMap_comp]
      apply WideSubcategory.hom_ext
      change (λ_ A.of).inv = (λ_ A).hom.iso.inv ≫ 𝟙 _
      simp only [Category.comp_id]
      rfl
    · apply WideSubcategory.hom_ext
      change (λ_ A.of).hom = 𝟙 _ ≫ (λ_ A).hom.iso.hom
      simp only [Category.id_comp]
      rfl

end ModuleCat.FiniteProjective
