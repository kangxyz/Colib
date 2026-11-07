/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Cofinality.DenseSubcategory

/-! # The actual group of common-complement classes

Actual coproducts induce addition. Density supplies genuine complements,
which become inverses. The zero-class criterion is proved from the original
split cofiber, so it detects exact object membership in the full subcategory.

Implementation provenance: `Quillen/Waldhausen/Cofinality/ComplementGroup.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
maps, hypotheses and independent object/hom universes are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.Waldhausen.Cofinality.DenseCofiberData
variable {C : Type u} [Category.{v} C] {W : Structure C} [HasBinaryCoproducts C]
  {P : ObjectProperty C} (h : DenseCofiberData W P)

/-- The actual quotient of original objects by their common-complement relation. -/
abbrev Classes := Quotient h.setoid

/-- The class of the original object itself. -/
def classOf (A : C) : h.Classes := Quotient.mk _ A

/-- Equality of object classes retains an actual common-complement witness. -/
theorem classOf_eq_iff (A B : C) : h.classOf A = h.classOf B ↔ h.Related A B := Quotient.eq

instance : Zero h.Classes := ⟨h.classOf W.zero⟩
instance : Add h.Classes := ⟨Quotient.map₂ (fun A B : C ↦ A ⨿ B)
  (fun _ _ hab _ _ hde ↦ h.related_coprod hab hde)⟩

/-- The actual zero class has precisely the original chosen-zero representative. -/
@[simp] theorem classOf_zero : h.classOf W.zero = 0 := rfl

/-- Addition is induced by the actual original categorical coproduct. -/
@[simp] theorem classOf_coprod (A B : C) : h.classOf (A ⨿ B) = h.classOf A + h.classOf B := rfl

/-- Zero class is exactly actual subcategory membership, not a formal saturation. -/
theorem classOf_eq_zero_iff (A : C) : h.classOf A = 0 ↔ P A :=
  (h.classOf_eq_iff A W.zero).trans (h.related_zero_iff A)

instance : AddCommMonoid h.Classes where
  add_assoc a b c := Quotient.inductionOn₃ a b c (fun A B D ↦
    Quotient.sound (h.related_of_iso (coprod.associator A B D)))
  zero_add a := Quotient.inductionOn a (fun A ↦
    Quotient.sound (h.related_of_iso (zeroCoprodIso (W := W) A)))
  add_zero a := Quotient.inductionOn a (fun A ↦
    Quotient.sound (h.related_of_iso (coprod.braiding A W.zero ≪≫ zeroCoprodIso (W := W) A)))
  add_comm a b := Quotient.inductionOn₂ a b (fun A B ↦
    Quotient.sound (h.related_of_iso (coprod.braiding A B)))
  nsmul := nsmulRec

/-- A genuine chosen complement of a representative supplies the inverse class. -/
instance : Neg h.Classes := ⟨fun a ↦ h.classOf (h.complement a.out).choose⟩

/-- The inverse identity uses the actual complement and its proved membership. -/
theorem neg_add_cancel (a : h.Classes) : -a + a = 0 := by
  let B := (h.complement a.out).choose
  have hB : P (a.out ⨿ B) := (h.complement a.out).choose_spec
  calc
    -a + a = h.classOf B + h.classOf a.out := congrArg (fun b ↦ h.classOf B + b)
      (Quotient.out_eq a).symm
    _ = h.classOf (B ⨿ a.out) := rfl
    _ = 0 := (h.classOf_eq_zero_iff _).mpr ((h.iso_iff (coprod.braiding _ _)).mp hB)

instance : AddCommGroup h.Classes where
  neg_add_cancel := h.neg_add_cancel
  zsmul := zsmulRec

/-- Every actual class has an original object representative without an additional hypothesis. -/
theorem classOf_surjective : Function.Surjective h.classOf := Quotient.mk_surjective

/-- Original weak arrows retain the exact original class. -/
theorem classOf_weak {A B : C} (f : A ⟶ B) (hf : W.weq f) : h.classOf A = h.classOf B :=
  (h.classOf_eq_iff A B).mpr (h.related_of_weak f hf)

end CategoryTheory.Waldhausen.Cofinality.DenseCofiberData
