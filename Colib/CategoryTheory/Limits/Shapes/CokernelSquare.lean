/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
Implementation provenance:
`Quillen/Aglib/CategoryTheory/Limits/Shapes/CokernelSquare.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # The pushout square induced by cokernels of a map and its composite -/
@[expose] public section
noncomputable section
universe v u
open CategoryTheory
namespace CategoryTheory.Limits
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- Cokernels of `j` and `j ≫ k` form a pushout square with their induced map. -/
theorem isPushout_of_cokernels {A B B' M Y : C}
    (j : A ⟶ B) (k : B ⟶ B') (q : B ⟶ M) (p : B' ⟶ Y) (r : M ⟶ Y)
    (zq : j ≫ q = 0) (zp : (j ≫ k) ≫ p = 0)
    (hq : IsColimit (CokernelCofork.ofπ q zq))
    (hp : IsColimit (CokernelCofork.ofπ p zp)) (w : k ≫ p = q ≫ r) :
    IsPushout k q p r := by
  let : Epi q := Cofork.IsColimit.epi hq
  let : Epi p := Cofork.IsColimit.epi hp
  refine IsPushout.mk' w ?_ ?_
  · intro T a b hab _
    exact (cancel_epi p).1 hab
  · intro T a b hab
    have ha : (j ≫ k) ≫ a = 0 := by
      rw [Category.assoc, hab, ← Category.assoc, zq, zero_comp]
    let l := hp.desc (CokernelCofork.ofπ a ha)
    have hl : p ≫ l = a := hp.fac _ WalkingParallelPair.one
    refine ⟨l, hl, ?_⟩
    apply (cancel_epi q).1
    rw [← Category.assoc, ← w, Category.assoc, hl]
    exact hab

end CategoryTheory.Limits
