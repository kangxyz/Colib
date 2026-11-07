/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.GrothendieckComparison.ObjectNaturality
public import Colib.KTheory.Waldhausen.Additivity.GroupFormula
public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.Cofiber

/-! # Original cofibration-pushout relations in actual Waldhausen K₀

The proved structural extension-category additivity, evaluated on the original
canonical object class, gives the cofiber relation. Actual pushout pasting then
gives the full displayed pushout relation. No factorization or cylinder data
are required; the current extension-functor API is used for small categories.

Implementation provenance: `Quillen/Waldhausen/GrothendieckComparison/CofiberRelations.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
objects, maps and hypotheses are retained.
-/
@[expose] public section

noncomputable section
open Topology SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u
namespace CategoryTheory.Waldhausen.Structure
variable {C : Type u} [SmallCategory C] (W : Structure C)

/-- A displayed original cofiber sequence has its expected relation in the
original homotopical K₀ group law, in source-then-quotient order. -/
theorem kZeroObjectClass_cofiber {A B Q : C} {i : A ⟶ B} {q : B ⟶ Q}
    (hi : W.cof i) (hQ : IsPushout i (W.isZero.from_ A) q (W.isZero.to_ Q)) :
    W.kZeroObjectClass B = W.kZeroObjectClass A * W.kZeroObjectClass Q := by
  let : HasBinaryCoproducts C := Additivity.hasBinaryCoproducts W
  let X : ExtensionCategory.Obj W := ⟨Arrow.mk i, hi⟩
  have h := Additivity.KMap_additivity_mul (ExtensionCategory.waldhausenStructure W) W
    (ExtensionCategory.inclusion W) (ExtensionCategory.quotient W)
    (ExtensionCategory.isCofibrationSequence W) 0
    ((ExtensionCategory.waldhausenStructure W).kZeroObjectClass X)
  simp only [KMap_kZeroObjectClass] at h
  change W.kZeroObjectClass B = W.kZeroObjectClass A *
    W.kZeroObjectClass ((ExtensionCategory.cofiber W).obj X) at h
  let e : (ExtensionCategory.cofiber W).obj X ≅ Q :=
    (ExtensionCategory.cofiber_isPushout W X).isoIsPushout _ _ hQ
  exact h.trans (congrArg (W.kZeroObjectClass A * ·) (W.kZeroObjectClass_iso e))

/-- Every displayed original cofibration pushout gives the original signed
Grothendieck relation in the actual homotopical Waldhausen K₀. -/
theorem kZeroObjectClass_pushout {A B D Q : C} {i : A ⟶ B} {f : A ⟶ D}
    {g : B ⟶ Q} {j : D ⟶ Q} (hi : W.cof i) (hQ : IsPushout i f g j) :
    W.kZeroObjectClass Q =
      W.kZeroObjectClass B * W.kZeroObjectClass D * (W.kZeroObjectClass A)⁻¹ := by
  let : CommGroup (W.K 0) := Additivity.KCommGroup W 0
  have hj := W.cof_pushout hi hQ
  obtain ⟨R, q, r, hR⟩ := W.pushout_exists j (W.isZero.from_ D) hj
  have hr : r = W.isZero.to_ R := W.isZero.eq_of_src _ _
  subst r
  have hcomp := hQ.paste_vert hR
  have hf0 : f ≫ W.isZero.from_ D = W.isZero.from_ A := W.isZero.eq_of_tgt _ _
  rw [hf0] at hcomp
  have hB := W.kZeroObjectClass_cofiber hi hcomp
  have hD := W.kZeroObjectClass_cofiber hj hR
  rw [hB, hD]
  simp [mul_comm, mul_left_comm]

end CategoryTheory.Waldhausen.Structure
