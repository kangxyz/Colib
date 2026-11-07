/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # A specified cokernel as the pushout along a zero object

Adapted from Quillen/Aglib/CategoryTheory/Limits/Shapes/CokernelPushout.lean
at c561118b7795eb9780be9ed391c3251d6a4d0afd, retaining the actual displayed maps.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.Limits
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- The original cokernel and any two maps through a zero object form a pushout. -/
theorem isPushout_of_isColimit_cokernel
    {A B Q Z : C} {f : A ⟶ B} {q : B ⟶ Q} (hfq : f ≫ q = 0)
    (hc : IsColimit (CokernelCofork.ofπ q hfq)) (hZ : IsZero Z)
    (az : A ⟶ Z) (zq : Z ⟶ Q) : IsPushout f az q zq := by
  have w : f ≫ q = az ≫ zq := by
    rw [hfq, hZ.eq_zero_of_src zq, comp_zero]
  have hzero (s : PushoutCocone f az) : f ≫ s.inl = 0 := by
    rw [s.condition, hZ.eq_zero_of_src s.inr, comp_zero]
  apply IsPushout.of_isColimit (c := PushoutCocone.mk q zq w)
  refine PushoutCocone.IsColimit.mk w
    (fun s ↦ (CokernelCofork.IsColimit.desc' hc s.inl (hzero s)).1) ?_ ?_ ?_
  · intro s
    exact (CokernelCofork.IsColimit.desc' hc s.inl (hzero s)).2
  · intro s
    exact hZ.eq_of_src _ _
  · intro s m hm _
    apply Cofork.IsColimit.hom_ext hc
    exact hm.trans (CokernelCofork.IsColimit.desc' hc s.inl (hzero s)).2.symm

end CategoryTheory.Limits
