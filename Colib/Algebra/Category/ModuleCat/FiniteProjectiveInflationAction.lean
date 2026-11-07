/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensions
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveMonoidal
public import Colib.CategoryTheory.ExactCategory.ExtensionTotal
public import Colib.CategoryTheory.ExactCategory.Isomorphisms
public import Mathlib.CategoryTheory.Monoidal.Action.Basic

/-!
Implementation provenance:
`Quillen/Algebra/Category/ModuleCat/FiniteProjectiveInflationAction.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Direct-sum action on admissible inflations of finite projective modules -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]
attribute [local instance] categoryDirectSumMonoidal categoryDirectSumSymmetric
attribute [local instance] directSumMonoidal directSumSymmetric

/-- Direct sum acts on the actual category of admissible inflations. -/
@[instance_reducible]
def inflationDirectSumAction :
    MonoidalLeftAction (IsoCategory R) (exactStructure R).InflationCategory where
  actionObj S X := ⟨S.of ⊗ X.obj⟩
  actionHomLeft f X := ⟨f.iso.hom ▷ X.obj,
    (exactStructure R).inflation_of_iso (whiskerRightIso f.iso X.obj)⟩
  actionHomRight S _ _ f := ⟨S.of ◁ f.hom, inflation_coprod_map_id R S.of f.hom f.property⟩
  actionAssocIso S T X := WideSubcategory.isoMk (α_ S.of T.of X.obj)
    ((exactStructure R).inflation_of_iso (α_ S.of T.of X.obj))
    ((exactStructure R).inflation_of_iso (α_ S.of T.of X.obj).symm)
  actionUnitIso X := WideSubcategory.isoMk (λ_ X.obj)
    ((exactStructure R).inflation_of_iso (λ_ X.obj))
    ((exactStructure R).inflation_of_iso (λ_ X.obj).symm)

  actionAssocIso_hom_naturality := by
    intro c₁ c₂ c₃ c₄ d₁ d₂ f g h
    apply WideSubcategory.hom_ext
    change (((f.iso.hom ⊗ₘ g.iso.hom) ▷ d₁.obj) ≫
      (c₂.of ⊗ c₄.of) ◁ h.hom) ≫ (α_ c₂.of c₄.of d₂.obj).hom =
      (α_ c₁.of c₃.of d₁.obj).hom ≫
        (f.iso.hom ▷ (c₃.of ⊗ d₁.obj) ≫
          c₂.of ◁ (g.iso.hom ▷ d₁.obj ≫ c₄.of ◁ h.hom))
    simpa only [← tensorHom_def] using associator_naturality f.iso.hom g.iso.hom h.hom
  actionUnitIso_hom_naturality := by
    intro X Y f
    apply WideSubcategory.hom_ext
    change (λ_ X.obj).hom ≫ f.hom = (𝟙_ (Category R)) ◁ f.hom ≫ (λ_ Y.obj).hom
    exact (leftUnitor_naturality f.hom).symm
  whiskerLeft_actionHomLeft := by
    intro S T U f X
    apply WideSubcategory.hom_ext
    change (S.of ◁ f.iso.hom) ▷ X.obj =
      (α_ S.of T.of X.obj).hom ≫ S.of ◁ (f.iso.hom ▷ X.obj) ≫ (α_ S.of U.of X.obj).inv
    exact MonoidalLeftAction.whiskerLeft_actionHomLeft S.of f.iso.hom X.obj
  whiskerRight_actionHomLeft := by
    intro S T U f X
    apply WideSubcategory.hom_ext
    change (f.iso.hom ▷ U.of) ▷ X.obj =
      (α_ S.of U.of X.obj).hom ≫ f.iso.hom ▷ (U.of ⊗ X.obj) ≫ (α_ T.of U.of X.obj).inv
    exact MonoidalLeftAction.whiskerRight_actionHomLeft U.of f.iso.hom X.obj
  associator_actionHom := by
    intro S T U X
    apply WideSubcategory.hom_ext
    change (α_ S.of T.of U.of).hom ▷ X.obj ≫ (α_ S.of (T.of ⊗ U.of) X.obj).hom ≫
      S.of ◁ (α_ T.of U.of X.obj).hom =
      (α_ (S.of ⊗ T.of) U.of X.obj).hom ≫ (α_ S.of T.of (U.of ⊗ X.obj)).hom
    exact pentagon S.of T.of U.of X.obj
  leftUnitor_actionHom := by
    intro S X
    apply WideSubcategory.hom_ext
    change (λ_ S.of).hom ▷ X.obj =
      (α_ (𝟙_ (Category R)) S.of X.obj).hom ≫ (λ_ (S.of ⊗ X.obj)).hom
    exact MonoidalLeftAction.leftUnitor_actionHom S.of X.obj
  rightUnitor_actionHom := by
    intro S X
    apply WideSubcategory.hom_ext
    change (ρ_ S.of).hom ▷ X.obj =
      (α_ S.of (𝟙_ (Category R)) X.obj).hom ≫ S.of ◁ (λ_ X.obj).hom
    exact MonoidalLeftAction.rightUnitor_actionHom S.of X.obj

end ModuleCat.FiniteProjective
