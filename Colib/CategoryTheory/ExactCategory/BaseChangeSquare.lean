/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.KernelPullback

/-!
Implementation provenance:
`Quillen/Aglib/CategoryTheory/ExactCategory/BaseChangeSquare.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Conflations on given pullback squares

An arbitrary pullback of a deflation retains its original kernel object.
The resulting conflation uses the original square and specified kernel map,
without replacing them by chosen limits or assuming global pullbacks.
-/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C)

/-- A given pullback of a deflation forms a conflation with the original
kernel object and any specified compatible kernel map. -/
theorem conflation_of_isPullback {S : ShortComplex C} (hS : E.conflation S)
    {P T : C} {k : P ⟶ S.X₂} {q : P ⟶ T} {f : T ⟶ S.X₃}
    (sq : IsPullback k q S.g f) (i : S.X₁ ⟶ P)
    (hi : i ≫ k = S.f) (z : i ≫ q = 0) :
    E.conflation (ShortComplex.mk i q z) := by
  let hk := E.kernel S hS
  let : Mono S.f := Fork.IsLimit.mono hk
  apply E.conflation_of_deflation_of_isKernel
    (E.deflation.of_isPullback sq (E.deflation_of_conflation hS))
  refine KernelFork.IsLimit.ofι i z
    (fun {W} a ha => hk.lift (KernelFork.ofι (a ≫ k) (by
      rw [Category.assoc, sq.w, ← Category.assoc, ha, zero_comp]))) ?_ ?_
  · intro W a ha
    apply sq.hom_ext
    · rw [Category.assoc, hi]
      exact hk.fac _ WalkingParallelPair.zero
    · simp only [Category.assoc, z, comp_zero, ha]
  · intro W a ha m hm
    apply (cancel_mono S.f).1
    calc
      m ≫ S.f = a ≫ k := by rw [← hi, ← Category.assoc, hm]
      _ = _ := by
        symm
        exact hk.fac (KernelFork.ofι (a ≫ k) (by
          rw [Category.assoc, sq.w, ← Category.assoc, ha, zero_comp])) WalkingParallelPair.zero

end CategoryTheory.ExactCategory.ExactStructure
