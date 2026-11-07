/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionCoherence
public import Colib.CategoryTheory.GroupCompletion.TrivialAction
public import Colib.CategoryTheory.GroupCompletion.Functoriality

/-!
Implementation provenance:
`Quillen/Algebra/Category/ModuleCat/FiniteProjectiveExtensionLinear.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # The original quotient projection as a linear functor -/
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
attribute [local instance] MonoidalLeftAction.trivial

/-- The quotient projection is linear for the direct-sum action on extensions
and the trivial action on the original Q-category. -/
@[instance_reducible]
def extensionProjectionLinear :
    (exactStructure R).extensionProjection.LaxLeftLinear (IsoCategory R) where
  μₗ S x := ((exactStructure R).qIsoOfIso (directSumExtensionQuotientIso R S x)).inv
  μₗ_naturality_left := by
    intro S T f x
    apply (cancel_mono ((exactStructure R).qIsoOfIso
      (directSumExtensionQuotientIso R T x)).hom).1
    have h := directSumProjection_naturality R f (𝟙 x)
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    change 𝟙 _ = ((exactStructure R).qIsoOfIso
      (directSumExtensionQuotientIso R S x)).inv ≫
        (exactStructure R).extensionProjectionQMap (Subdivision.actionMap f (𝟙 x)) ≫
          ((exactStructure R).qIsoOfIso (directSumExtensionQuotientIso R T x)).hom
    rw [h]
    simp
    rfl
  μₗ_naturality_right := by
    intro S x y f
    apply (cancel_mono ((exactStructure R).qIsoOfIso
      (directSumExtensionQuotientIso R S y)).hom).1
    have h := directSumProjection_naturality R (𝟙 S) f
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    change (exactStructure R).extensionProjectionQMap f =
      ((exactStructure R).qIsoOfIso (directSumExtensionQuotientIso R S x)).inv ≫
        (exactStructure R).extensionProjectionQMap (Subdivision.actionMap (𝟙 S) f) ≫
          ((exactStructure R).qIsoOfIso (directSumExtensionQuotientIso R S y)).hom
    rw [h]
    simp
  μₗ_associativity := by
    intro S T x
    change _ ≫ (exactStructure R).extensionProjectionQMap (αₗ S T x).hom = _
    rw [directSumProjection_associator]
    simp only [directSumAssociatorQuotientIso, Iso.trans_symm,
      CategoryTheory.ExactCategory.ExactStructure.qIsoOfIso_trans, Iso.trans_hom,
        Iso.inv_hom_id_assoc]
    change _ = 𝟙 _ ≫
      ((exactStructure R).qIsoOfIso (directSumExtensionQuotientIso R T x)).inv ≫
      ((exactStructure R).qIsoOfIso
        (directSumExtensionQuotientIso R S (directSumExtensionObject R T x))).inv
    rw [Category.id_comp]
    rfl
  μₗ_unitality := by
    intro x
    change 𝟙 _ = _ ≫ (exactStructure R).extensionProjectionQMap (λₗ[IsoCategory R] x).hom
    rw [directSumProjection_unit]
    simp

end ModuleCat.FiniteProjective
