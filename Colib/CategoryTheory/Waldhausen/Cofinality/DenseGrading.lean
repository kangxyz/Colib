/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Cofinality.ComplementGroup
public import Colib.CategoryTheory.Waldhausen.Additivity.CoproductCofiber
public import Mathlib.Tactic.Abel

/-! # The genuine additive grading constructed from categorical density

Actual coproduct/cofiber squares show that the middle and source-plus-quotient
have a common original complement. The resulting full pushout valuation is
therefore proved. Its zero equation is exactly original subcategory membership,
rather than a grading or algebraic class criterion assumed as input.

Implementation provenance: `Quillen/Waldhausen/Cofinality/DenseGrading.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
maps, hypotheses and independent object/hom universes are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.Waldhausen.Cofinality
variable {C : Type u} [Category.{v} C] (W : Structure C) [HasBinaryCoproducts C]

namespace DenseCofiberData
variable {W} {P : ObjectProperty C} (h : DenseCofiberData W P)
include h

/-- The actual middle and the actual source-plus-quotient have a concrete common complement. -/
theorem related_cofiber {A B Q : C} {i : A ⟶ B} {q : B ⟶ Q}
    (hi : W.cof i) (hQ : IsPushout i (W.isZero.from_ A) q (W.isZero.to_ Q)) :
    h.Related B (A ⨿ Q) := by
  obtain ⟨A', hA'⟩ := h.complement A
  obtain ⟨Q', hQ'⟩ := h.complement Q
  have hm : P (B ⨿ (Q' ⨿ A')) := h.extension
    (Additivity.coprod_map_cof W i coprod.inr hi (Additivity.coprod_inr_cof W Q' A'))
    (Additivity.coprod_cofiber_isPushout W hi (Additivity.coprod_inr_cof W Q' A') hQ
      (Additivity.coprod_inr_cofiber W Q' A')) hA' hQ'
  refine ⟨A' ⨿ Q', (h.iso_iff (coprod.mapIso (Iso.refl B) (coprod.braiding Q' A'))).mp hm, ?_⟩
  exact (h.iso_iff (coprodFourSwap A A' Q Q')).mp (h.coprod_mem hA' hQ')

/-- Actual common-complement classes are additive on every original cofiber sequence. -/
theorem classOf_cofiber {A B Q : C} {i : A ⟶ B} {q : B ⟶ Q}
    (hi : W.cof i) (hQ : IsPushout i (W.isZero.from_ A) q (W.isZero.to_ Q)) :
    h.classOf B = h.classOf A + h.classOf Q :=
  (h.classOf_eq_iff B (A ⨿ Q)).mpr (h.related_cofiber hi hQ)

/-- The two actual cofibers of an original pushout give its full additive valuation. -/
theorem classOf_pushout {A B D Q : C} {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ Q} {j : D ⟶ Q}
    (hi : W.cof i) (hQ : IsPushout i f g j) :
    h.classOf Q = h.classOf B + h.classOf D - h.classOf A := by
  obtain ⟨R, q, z, hR⟩ := W.pushout_exists i (W.isZero.from_ A) hi
  have hz : z = W.isZero.to_ R := W.isZero.eq_of_src _ _
  subst z
  have hR' : IsPushout i (f ≫ W.isZero.from_ D) q (W.isZero.to_ R) := by
    simpa only [W.isZero.eq_of_tgt (f ≫ W.isZero.from_ D) (W.isZero.from_ A)] using hR
  have hbot := hR'.of_top' hQ
  have hb := h.classOf_cofiber hi hR
  have hc := h.classOf_cofiber (W.cof_pushout hi hQ) hbot
  rw [hb, hc]
  abel

/-- Actual density and cofiber closure construct a genuine grading detecting exact membership. -/
def grading : Grading W h.Classes where
  value := h.classOf
  zero := h.classOf_zero
  weak := h.classOf_weak
  pushout := h.classOf_pushout

/-- The grading's zero locus is the original full subcategory itself. -/
theorem grading_zero_iff (A : C) : h.grading.value A = 0 ↔ P A := h.classOf_eq_zero_iff A

/-- The genuine acyclic predicate is precisely the original object predicate. -/
theorem grading_acyclicObjects_iff (A : C) : Fibration.acyclicObjects h.grading.nested A ↔ P A :=
  (h.grading.acyclicObjects_iff A).trans (h.grading_zero_iff A)

end DenseCofiberData
end CategoryTheory.Waldhausen.Cofinality
