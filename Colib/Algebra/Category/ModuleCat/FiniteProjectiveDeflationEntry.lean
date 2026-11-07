/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.ExactCategory.ExtensionDeflationEntry
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionAction
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionLinear
public import Colib.CategoryTheory.Monoidal.Action.IsoFiber

/-!
Implementation provenance:
`Quillen/Algebra/Category/ModuleCat/FiniteProjectiveDeflationEntry.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Direct-sum equivariance of the actual fixed-deflation entry -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalLeftAction
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal inflationDirectSumAction
attribute [local instance] extensionFiberDirectSumAction

/-- The actual quotient identification for the two choices of the added kernel. -/
def extensionDeflationAddQuotientIso (C : Category.{u, u} R) (S : IsoCategory R)
    (p : (exactStructure R).ExtensionFiber C) :
    ((exactStructure R).extensionQuotientData
      (S ⊙ₗ (exactStructure R).extensionOfDeflation p.of)).obj ≅
    ((exactStructure R).extensionQuotientData
      ((exactStructure R).extensionOfDeflation (S ⊙ₗ p).of)).obj :=
  directSumExtensionQuotientIso R S ((exactStructure R).extensionOfDeflation p.of) ≪≫
    (exactStructure R).extensionOfDeflationQuotientIso p.of ≪≫
      ((exactStructure R).extensionOfDeflationQuotientIso (S ⊙ₗ p).of).symm

/-- Kernel choices commute with direct sum through the unique isomorphism
whose original middle-object map is the identity. -/
def extensionDeflationAddIso (C : Category.{u, u} R) (S : IsoCategory R)
    (p : (exactStructure R).ExtensionFiber C) :
    S ⊙ₗ (exactStructure R).extensionOfDeflation p.of ≅
      (exactStructure R).extensionOfDeflation (S ⊙ₗ p).of :=
  (exactStructure R).extensionIsoOfQuotientSquare (Iso.refl _)
    (extensionDeflationAddQuotientIso R C S p) (by
      apply (cancel_mono
        ((exactStructure R).extensionOfDeflationQuotientIso (S ⊙ₗ p).of).hom).1
      simp only [extensionDeflationAddQuotientIso, Iso.trans_hom, Iso.symm_hom,
        Iso.refl_hom, Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id,
        CategoryTheory.ExactCategory.ExactStructure.extensionOfDeflationQuotientIso_π]
      rw [← Category.assoc]
      have h := congrArg
        (fun z ↦ z ≫ ((exactStructure R).extensionOfDeflationQuotientIso p.of).hom)
        (directSumExtensionQuotientIso_π R S ((exactStructure R).extensionOfDeflation p.of))
      refine h.trans ?_
      change coprod.desc 0 _ ≫ _ = coprod.desc 0 _
      apply coprod.hom_ext <;> simp)

/-- The identity-middle kernel comparison has its precise original quotient map. -/
lemma extensionDeflationAddIso_projection (C : Category.{u, u} R) (S : IsoCategory R)
    (p : (exactStructure R).ExtensionFiber C) :
    (exactStructure R).extensionProjectionQMap (extensionDeflationAddIso R C S p).hom =
      ((exactStructure R).qIsoOfIso (extensionDeflationAddQuotientIso R C S p)).hom := by
  unfold extensionDeflationAddIso
  exact (exactStructure R).extensionIsoOfQuotientSquare_projection _ _ _

/-- The chosen-kernel entry is genuinely linear for the two original actions. -/
@[instance_reducible]
def extensionDeflationEntryLinear (C : Category.{u, u} R) :
    ((exactStructure R).extensionDeflationEntry C).LaxLeftLinear (IsoCategory R) where
  μₗ S p := (extensionDeflationAddIso R C S p).hom
  μₗ_naturality_left := by
    intro S T f p
    apply (exactStructure R).extensionTotalMiddle.map_injective
    change ((f.iso.hom ▷ p.of.obj.left) ≫ T.of ◁ 𝟙 _) ≫ 𝟙 _ =
      𝟙 _ ≫ (f.iso.hom ⊗ₘ 𝟙 _)
    simp only [← tensorHom_def, Category.id_comp, Category.comp_id]
  μₗ_naturality_right := by
    intro S p q f
    apply (exactStructure R).extensionTotalMiddle.map_injective
    change ((𝟙 S.of ▷ p.of.obj.left) ≫ S.of ◁ f.iso.hom.hom.left) ≫ 𝟙 _ =
      𝟙 _ ≫ (𝟙 S.of ⊗ₘ f.iso.hom.hom.left)
    simp only [← tensorHom_def, Category.id_comp, Category.comp_id]
  μₗ_associativity := by
    intro S T p
    apply (exactStructure R).extensionTotalMiddle.map_injective
    change 𝟙 _ ≫ (α_ S.of T.of p.of.obj.left).hom =
      (α_ S.of T.of p.of.obj.left).hom ≫
        ((𝟙 S.of ▷ (T.of ⊗ p.of.obj.left)) ≫ S.of ◁ 𝟙 _) ≫ 𝟙 _
    simp
  μₗ_unitality := by
    intro p
    apply (exactStructure R).extensionTotalMiddle.map_injective
    change (λ_ p.of.obj.left).hom = 𝟙 _ ≫ (λ_ p.of.obj.left).hom
    simp

/-- The original Q target carries the named trivial action only in this file. -/
local instance quotientTrivialAction : MonoidalLeftAction (IsoCategory R)
    (QConstruction (exactStructure R).deflation (exactStructure R).inflation) :=
  MonoidalLeftAction.trivial _ _

attribute [local instance] extensionProjectionLinear

/-- All original quotient lineators are actual isomorphisms. -/
local instance quotientLineatorIsIso (S : IsoCategory R)
    (x : (exactStructure R).ExtensionTotal) :
    IsIso (Functor.LaxLeftLinear.μₗ (exactStructure R).extensionProjection S x) := by
  change IsIso (((exactStructure R).qIsoOfIso (directSumExtensionQuotientIso R S x)).inv)
  infer_instance

/-- Direct sum on the actual original-Q isomorphism fiber. -/
@[instance_reducible]
def extensionIsoFiberDirectSumAction (C : Category.{u, u} R) :
    MonoidalLeftAction (IsoCategory R)
      (IsoFiber (exactStructure R).extensionProjection
        (QConstruction.of (exactStructure R).deflation (exactStructure R).inflation C)) :=
  IsoFiber.monoidalLeftAction _ _

attribute [local instance] extensionIsoFiberDirectSumAction

/-- The same identity-middle isomorphism respects the specified original-Q
structure maps, so it is a genuine arrow of the isomorphism fiber. -/
def extensionDeflationIsoFiberLineator (C : Category.{u, u} R) (S : IsoCategory R)
    (p : (exactStructure R).ExtensionFiber C) :
    S ⊙ₗ ((exactStructure R).extensionDeflationIsoFiber C).obj p ⟶
      ((exactStructure R).extensionDeflationIsoFiber C).obj (S ⊙ₗ p) :=
  ((isoFiberProperty (exactStructure R).extensionProjection
    (QConstruction.of (exactStructure R).deflation (exactStructure R).inflation C)).isoMk
    (StructuredArrow.isoMk (extensionDeflationAddIso R C S p) (by
    change (((exactStructure R).qIsoOfIso
      ((exactStructure R).extensionOfDeflationQuotientIso p.of)).inv ≫
      ((exactStructure R).qIsoOfIso (directSumExtensionQuotientIso R S
        ((exactStructure R).extensionOfDeflation p.of))).inv) ≫
      (exactStructure R).extensionProjectionQMap (extensionDeflationAddIso R C S p).hom =
      ((exactStructure R).qIsoOfIso
        ((exactStructure R).extensionOfDeflationQuotientIso (S ⊙ₗ p).of)).inv
    rw [extensionDeflationAddIso_projection]
    simp only [extensionDeflationAddQuotientIso,
      CategoryTheory.ExactCategory.ExactStructure.qIsoOfIso_trans,
      Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
    rfl))).hom

/-- The fixed-deflation equivalence is linear for the genuine induced fiber action. -/
@[instance_reducible]
def extensionDeflationIsoFiberLinear (C : Category.{u, u} R) :
    ((exactStructure R).extensionDeflationIsoFiber C).LaxLeftLinear (IsoCategory R) where
  μₗ := extensionDeflationIsoFiberLineator R C
  μₗ_naturality_left := by
    intro S T f p
    apply ObjectProperty.hom_ext
    apply StructuredArrow.hom_ext
    apply (exactStructure R).extensionTotalMiddle.map_injective
    change ((f.iso.hom ▷ p.of.obj.left) ≫ T.of ◁ 𝟙 _) ≫ 𝟙 _ =
      𝟙 _ ≫ (f.iso.hom ⊗ₘ 𝟙 _)
    simp only [← tensorHom_def, Category.id_comp, Category.comp_id]
  μₗ_naturality_right := by
    intro S p q f
    apply ObjectProperty.hom_ext
    apply StructuredArrow.hom_ext
    apply (exactStructure R).extensionTotalMiddle.map_injective
    change ((𝟙 S.of ▷ p.of.obj.left) ≫ S.of ◁ f.iso.hom.hom.left) ≫ 𝟙 _ =
      𝟙 _ ≫ (𝟙 S.of ⊗ₘ f.iso.hom.hom.left)
    simp only [← tensorHom_def, Category.id_comp, Category.comp_id]
  μₗ_associativity := by
    intro S T p
    apply ObjectProperty.hom_ext
    apply StructuredArrow.hom_ext
    apply (exactStructure R).extensionTotalMiddle.map_injective
    change 𝟙 _ ≫ (α_ S.of T.of p.of.obj.left).hom =
      (α_ S.of T.of p.of.obj.left).hom ≫
        ((𝟙 S.of ▷ (T.of ⊗ p.of.obj.left)) ≫ S.of ◁ 𝟙 _) ≫ 𝟙 _
    simp
  μₗ_unitality := by
    intro p
    apply ObjectProperty.hom_ext
    apply StructuredArrow.hom_ext
    apply (exactStructure R).extensionTotalMiddle.map_injective
    change (λ_ p.of.obj.left).hom = 𝟙 _ ≫ (λ_ p.of.obj.left).hom
    simp

attribute [local instance] extensionDeflationIsoFiberLinear

/-- The actual fiber lineator is invertible, with the already constructed
identity-middle extension isomorphism as its underlying isomorphism. -/
instance extensionDeflationIsoFiberLineator_isIso (C : Category.{u, u} R)
    (S : IsoCategory R) (p : (exactStructure R).ExtensionFiber C) :
    IsIso (Functor.LaxLeftLinear.μₗ
      ((exactStructure R).extensionDeflationIsoFiber C) S p) := by
  change IsIso (extensionDeflationIsoFiberLineator R C S p)
  unfold extensionDeflationIsoFiberLineator
  infer_instance

end ModuleCat.FiniteProjective
