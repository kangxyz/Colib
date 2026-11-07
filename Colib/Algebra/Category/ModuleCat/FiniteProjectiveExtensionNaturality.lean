/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionQuotient
public import Colib.CategoryTheory.ExactCategory.ExtensionProjectionGeometry
public import Colib.CategoryTheory.ExactCategory.QSpanNaturality
public import Colib.CategoryTheory.Subdivision.Action

/-!
Implementation provenance:
`Quillen/Algebra/Category/ModuleCat/FiniteProjectiveExtensionNaturality.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Naturality of the quotient isomorphisms under the actual direct-sum action -/
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
variable {S T : IsoCategory R} (u : S ⟶ T)
variable {x y : (exactStructure R).ExtensionTotal} (f : x ⟶ y)

local notation "E" => exactStructure R
local notation "af" => Subdivision.actionMap u f
local notation "qf" => CategoryTheory.ExactCategory.ExactStructure.extensionProjectionCokernel
  (exactStructure R) f
local notation "qa" => CategoryTheory.ExactCategory.ExactStructure.extensionProjectionCokernel
  (exactStructure R) (Subdivision.actionMap u f)

/-- The action reverses the actor map in the kernel coordinate. -/
theorem directSumAction_domainMap :
    (Subdivision.domainMap af).hom =
      coprod.map u.iso.inv (Subdivision.domainMap f).hom := by
  have hu : (inv u).iso.hom = u.iso.inv := by
    apply (cancel_epi u.iso.hom).1
    have hi := congrArg (fun a => a.iso.hom) (IsIso.hom_inv_id u)
    change u.iso.hom ≫ (inv u).iso.hom = 𝟙 S.of at hi
    simpa only [Iso.hom_inv_id] using hi
  rw [Subdivision.actionMap_domainMap]
  change coprod.map (inv u).iso.hom (𝟙 _) ≫ coprod.map (𝟙 S.of) _ = _
  simp [hu]

/-- The action uses the forward actor map in the middle-object coordinate. -/
theorem directSumAction_base : (af).base.hom = coprod.map u.iso.hom f.base.hom := by
  change coprod.map u.iso.hom (𝟙 _) ≫ coprod.map (𝟙 T.of) _ = _
  simp

/-- A cokernel for the smaller subobject in an acted-on extension arrow. -/
def directSumProjectionApexCokernel :
    IsColimit (CokernelCofork.ofπ
      (coprod.desc (0 : S.of ⟶ _) (qf).π)
      (show ((Subdivision.domainMap af).hom ≫
        (directSumExtensionObject R S x).fiber.unop.hom.hom) ≫
          coprod.desc (0 : S.of ⟶ _) (qf).π = 0 by
        rw [directSumAction_domainMap]
        change (coprod.map u.iso.inv (Subdivision.domainMap f).hom ≫
          coprod.map (𝟙 S.of) x.fiber.unop.hom.hom) ≫ _ = 0
        simp only [Category.assoc, coprod.map_desc, Category.id_comp]
        apply coprod.hom_ext
        · simp
        · simpa only [coprod.inr_desc, comp_zero, Category.assoc] using (qf).zero)) := by
  let hc := isCokernelCoprodId S.of
    ((Subdivision.domainMap f).hom ≫ x.fiber.unop.hom.hom)
    (qf).π (qf).zero (qf).isColimit
  apply isCokernelEpiComp hc
    (coprod.map u.iso.inv (𝟙 y.fiber.unop.left.obj))
  rw [directSumAction_domainMap]
  change coprod.map u.iso.inv (Subdivision.domainMap f).hom ≫
      coprod.map (𝟙 S.of) x.fiber.unop.hom.hom =
    coprod.map u.iso.inv (𝟙 y.fiber.unop.left.obj) ≫
      coprod.map (𝟙 S.of)
        ((Subdivision.domainMap f).hom ≫ x.fiber.unop.hom.hom)
  simp

/-- The quotient-span apex isomorphism for a direct-sum action arrow. -/
def directSumProjectionApexIso : ((exactStructure R).extensionProjectionSpan af).apex ≅
    ((exactStructure R).extensionProjectionSpan f).apex :=
  (qa).isColimit.coconePointUniqueUpToIso (directSumProjectionApexCokernel R u f)

/-- The apex isomorphism preserves the actual quotient projection. -/
@[reassoc]
theorem directSumProjectionApexIso_π :
    (qa).π ≫ (directSumProjectionApexIso R u f).hom = coprod.desc (0 : S.of ⟶ _) (qf).π :=
  (qa).isColimit.comp_coconePointUniqueUpToIso_hom
    (directSumProjectionApexCokernel R u f) WalkingParallelPair.one

/-- Naturality in both the projective summand isomorphism and the original
extension arrow, proved in the original Q category. -/
theorem directSumProjection_naturality :
    (exactStructure R).extensionProjectionQMap af ≫
      ((exactStructure R).qIsoOfIso (directSumExtensionQuotientIso R T y)).hom =
    ((exactStructure R).qIsoOfIso (directSumExtensionQuotientIso R S x)).hom ≫
      (exactStructure R).extensionProjectionQMap f := by
  let eA := directSumProjectionApexIso R u f
  let : Epi (qa).π := Cofork.IsColimit.epi (qa).isColimit
  apply (exactStructure R).qSpan_iso_naturality _ _
    (directSumExtensionQuotientIso R S x) (directSumExtensionQuotientIso R T y) eA
  · apply (cancel_epi (qa).π).1
    rw [← Category.assoc, (qa).left]
    change ((exactStructure R).extensionQuotientData (directSumExtensionObject R S x)).π ≫
      (directSumExtensionQuotientIso R S x).hom =
        (qa).π ≫ ((directSumProjectionApexIso R u f).hom ≫
          ((exactStructure R).extensionProjectionSpan f).l)
    rw [directSumExtensionQuotientIso_π, ← Category.assoc, directSumProjectionApexIso_π]
    simp only [coprod.desc_comp, zero_comp, (qf).left]
  · apply (cancel_epi (qa).π).1
    rw [← Category.assoc, (qa).right, Category.assoc]
    change (af).base.hom ≫
      ((exactStructure R).extensionQuotientData (directSumExtensionObject R T y)).π ≫
        (directSumExtensionQuotientIso R T y).hom =
          (qa).π ≫ ((directSumProjectionApexIso R u f).hom ≫
            ((exactStructure R).extensionProjectionSpan f).r)
    rw [directSumExtensionQuotientIso_π, directSumAction_base,
      ← Category.assoc, directSumProjectionApexIso_π]
    simp only [coprod.map_desc, comp_zero, coprod.desc_comp, zero_comp, (qf).right]

end ModuleCat.FiniteProjective
