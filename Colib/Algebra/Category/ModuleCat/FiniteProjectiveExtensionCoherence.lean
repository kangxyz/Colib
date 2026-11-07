/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionEquivariance
public import Colib.CategoryTheory.ExactCategory.ExtensionProjectionIsomorphism

/-!
Implementation provenance:
`Quillen/Algebra/Category/ModuleCat/FiniteProjectiveExtensionCoherence.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Unit and associator coherence of the original extension quotient projection -/
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

/-- The action unitor maps to the canonical quotient isomorphism. -/
theorem directSumProjection_unit (x : (exactStructure R).ExtensionTotal) :
    (exactStructure R).extensionProjectionQMap (λₗ[IsoCategory R] x).hom =
      ((exactStructure R).qIsoOfIso
        (directSumExtensionQuotientIso R (𝟙_ (IsoCategory R)) x)).hom := by
  let : Epi (Subdivision.domainMap (λₗ[IsoCategory R] x).hom).hom := by
    change Epi (λ_ x.fiber.unop.left.obj).inv
    infer_instance
  apply (exactStructure R).extensionProjectionQMap_eq_qIsoOfIso
  change ((exactStructure R).extensionQuotientData
    (directSumExtensionObject R (𝟙_ (IsoCategory R)) x)).π ≫
      (directSumExtensionQuotientIso R (𝟙_ (IsoCategory R)) x).hom = _
  rw [directSumExtensionQuotientIso_π]
  change coprod.desc 0 ((exactStructure R).extensionQuotientData x).π =
    (λ_ x.base.obj).hom ≫ ((exactStructure R).extensionQuotientData x).π
  simp
  rfl

/-- The canonical quotient isomorphism associated to the action associator. -/
def directSumAssociatorQuotientIso (S T : IsoCategory R)
    (x : (exactStructure R).ExtensionTotal) :=
  directSumExtensionQuotientIso R (S ⊗ T) x ≪≫
    (directSumExtensionQuotientIso R S (directSumExtensionObject R T x) ≪≫
      directSumExtensionQuotientIso R T x).symm

/-- The action associator maps to the canonical quotient associator isomorphism. -/
theorem directSumProjection_associator (S T : IsoCategory R)
    (x : (exactStructure R).ExtensionTotal) :
    (exactStructure R).extensionProjectionQMap (αₗ S T x).hom =
      ((exactStructure R).qIsoOfIso (directSumAssociatorQuotientIso R S T x)).hom := by
  let : Epi (Subdivision.domainMap (αₗ S T x).hom).hom := by
    change Epi (α_ S.of T.of x.fiber.unop.left.obj).inv
    infer_instance
  apply (exactStructure R).extensionProjectionQMap_eq_qIsoOfIso
  let e := directSumExtensionQuotientIso R S (directSumExtensionObject R T x) ≪≫
    directSumExtensionQuotientIso R T x
  apply (cancel_mono e.hom).1
  change (((exactStructure R).extensionQuotientData
    (directSumExtensionObject R (S ⊗ T) x)).π ≫
      (directSumExtensionQuotientIso R (S ⊗ T) x).hom ≫ e.inv) ≫ e.hom =
    ((α_ S.of T.of x.base.obj).hom ≫
      ((exactStructure R).extensionQuotientData
        (directSumExtensionObject R S (directSumExtensionObject R T x))).π) ≫ e.hom
  rw [Category.assoc, Category.assoc, e.inv_hom_id, Category.comp_id,
    directSumExtensionQuotientIso_π]
  change coprod.desc 0 ((exactStructure R).extensionQuotientData x).π =
    (α_ S.of T.of x.base.obj).hom ≫
      ((exactStructure R).extensionQuotientData
        (directSumExtensionObject R S (directSumExtensionObject R T x))).π ≫
      (directSumExtensionQuotientIso R S (directSumExtensionObject R T x)).hom ≫
      (directSumExtensionQuotientIso R T x).hom
  rw [directSumExtensionQuotientIso_π_assoc, coprod.desc_comp, zero_comp,
    directSumExtensionQuotientIso_π]
  change coprod.desc 0 ((exactStructure R).extensionQuotientData x).π =
    (coprod.associator S.of T.of x.base.obj).hom ≫
      coprod.desc 0 (coprod.desc 0 ((exactStructure R).extensionQuotientData x).π)
  apply coprod.hom_ext
  · apply coprod.hom_ext <;> simp [coprod.associator]
  · simp [coprod.associator]

end ModuleCat.FiniteProjective
