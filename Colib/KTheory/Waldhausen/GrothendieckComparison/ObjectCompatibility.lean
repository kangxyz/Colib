/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.GrothendieckComparison.Naturality
public import Colib.KTheory.Waldhausen.GrothendieckComparison.ObjectLoops

/-! # The fine grading map retains the original canonical object classes
Implementation provenance: `Quillen/Waldhausen/GrothendieckComparison/ObjectCompatibility.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
objects, maps and hypotheses are retained.
-/
@[expose] public section

noncomputable section
open Topology SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u
namespace CategoryTheory.Waldhausen.Cofinality.Grading
variable {C G : Type u} [SmallCategory C] [AddCommGroup G]
  {W : Structure C} (d : Grading W G)

/-- The genuine original object simplex maps to precisely its original grade arrow. -/
@[simp] theorem fineGradeNerveMap_objectSimplex (X : C) :
    d.fineGradeNerveMap.app (op ⦋1⦌) (W.kZeroObjectSimplex X) =
      ComposableArrows.mk₁ (SingleObj.toEnd (Multiplicative G)
        (Multiplicative.ofAdd (d.value X))).asHom := by
  refine ComposableArrows.ext₁ (F := d.fineGradeNerveMap.app (op ⦋1⦌)
    (W.kZeroObjectSimplex X)) (G := _) rfl rfl ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- The actual realized object loop maps to the original group arrow loop,
with the exact chosen-basepoint transport. -/
theorem fineGradeNerveMap_objectLoop (X : C) :
    ((W.kZeroObjectLoop X).map (SSet.toTop.map d.fineGradeNerveMap).hom.continuous).cast
      d.fineGradeNerveMap_basepoint.symm d.fineGradeNerveMap_basepoint.symm =
        classifyingSpacePath (SingleObj.toEnd (Multiplicative G)
          (Multiplicative.ofAdd (d.value X))).asHom := by
  ext t
  change SSet.toTop.map d.fineGradeNerveMap (realizationEdgePath (W.kZeroObjectEdge X) t) = _
  exact (realizationEdgePath_naturality_apply d.fineGradeNerveMap
    (W.kZeroObjectEdge X) t).trans
      (congrArg (fun e : (nerve (SingleObj (Multiplicative G))) _⦋1⦌ ↦
        SSet.toTop.map (SSet.yonedaEquiv.symm e) (realizationInterval t))
          (d.fineGradeNerveMap_objectSimplex X))

/-- An original canonical homotopical object class has precisely its original grade. -/
@[simp] theorem fineKZeroMap_objectClass (X : C) :
    d.fineKZeroMap (W.kZeroObjectClass X) = Multiplicative.ofAdd (d.value X) := by
  apply (GroupoidClassifying.singleObjPiOneEquiv (Multiplicative G)).injective
  change GroupoidClassifying.singleObjPiOneEquiv _
    ((GroupoidClassifying.singleObjPiOneEquiv _).symm
      (d.fineKZeroToGroupPi (W.kZeroObjectClass X))) = _
  rw [MulEquiv.apply_symm_apply]
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  change HomotopyGroup.pi1MulEquivFundamentalGroup
    (HomotopyGroup.map (SSet.toTop.map d.fineGradeNerveMap).hom
      d.fineGradeNerveMap_basepoint (W.kZeroObjectClass X)) = _
  rw [HomotopyGroup.pi1MulEquivFundamentalGroup_naturality]
  change FundamentalGroup.mapOfEq _ _
    (W.kZeroFundamentalGroupEquiv (W.kZeroObjectClass X)) = _
  rw [W.kZeroFundamentalGroupEquiv_objectClass, FundamentalGroup.mapOfEq_apply]
  simp only [GroupoidClassifying.singleObjPiOneEquiv_apply]
  apply End.ext
  exact congrArg Path.Homotopic.Quotient.mk (d.fineGradeNerveMap_objectLoop X)

end CategoryTheory.Waldhausen.Cofinality.Grading

namespace CategoryTheory.Waldhausen.AlgebraicGrothendieck
variable {C : Type u} [SmallCategory C] (W : Structure C)

/-- The genuine homotopical-to-classical homomorphism preserves each original
canonical object class with its original weak-arrow/cofibration relations. -/
@[simp] theorem kZeroToGrothendieck_objectClass (X : C) :
    kZeroToGrothendieck W (W.kZeroObjectClass X) =
      Multiplicative.ofAdd (objectClass W X) :=
  (grading W).fineKZeroMap_objectClass X

/-- Every original classical Grothendieck class is the image of an actual K₀
class, by products and inverses of the original canonical object loops. -/
theorem kZeroToGrothendieck_surjective : Function.Surjective (kZeroToGrothendieck W) := by
  intro a
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk'_surjective (relations W) a.toAdd
  have hlift : ∃ x : W.K 0, kZeroToGrothendieck W x =
      Multiplicative.ofAdd (QuotientAddGroup.mk' (relations W) r) := by
    clear hr a
    induction r using FreeAbelianGroup.induction_on with
    | zero => exact ⟨1, by simp⟩
    | of X => exact ⟨W.kZeroObjectClass X, kZeroToGrothendieck_objectClass W X⟩
    | neg r ih =>
      obtain ⟨x, hx⟩ := ih
      exact ⟨x⁻¹, by simpa only [map_inv, map_neg, ofAdd_neg] using congrArg Inv.inv hx⟩
    | add r s hr hs =>
      obtain ⟨x, hx⟩ := hr
      obtain ⟨y, hy⟩ := hs
      exact ⟨x * y, by simp only [map_mul, hx, hy, map_add, ofAdd_add]⟩
  obtain ⟨x, hx⟩ := hlift
  exact ⟨x, hx.trans (congrArg Multiplicative.ofAdd hr)⟩

end CategoryTheory.Waldhausen.AlgebraicGrothendieck
