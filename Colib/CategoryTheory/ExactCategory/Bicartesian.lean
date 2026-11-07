/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.BaseChange

/-!
Implementation provenance:
`Quillen/Aglib/CategoryTheory/ExactCategory/Bicartesian.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Pushouts of admissible monomorphisms are bicartesian

The chosen pushout of an admissible monomorphism, and any other pushout
square on the same maps, is also a pullback. The proof uses only the
exact-category axioms: the pushed-out inflation retains the original cokernel.
No ambient abelian category or arbitrary limits are needed.
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

/-- A pushout of an admissible monomorphism is also a pullback. -/
theorem inflation_pushout_isPullback {A B A' : C} (i : A ⟶ B) (f : A ⟶ A')
    (hi : E.inflation i) [HasPushout i f] :
    IsPullback i f (pushout.inl i f) (pushout.inr i f) := by
  obtain ⟨Q, p, z, c⟩ := hi
  let hk := E.kernel (ShortComplex.mk i p z) c
  let c' := E.pushoutConflation_mem c f
  let : Mono i := Fork.IsLimit.mono hk
  let : Mono (pushout.inr i f) := E.mono_of_inflation (E.inflation_of_conflation c')
  refine IsPullback.mk' pushout.condition ?_ ?_
  · intro T a b hab _
    exact (cancel_mono i).1 hab
  · intro T a b hab
    have ha : a ≫ p = 0 := by
      calc
        a ≫ p = a ≫ pushout.inl i f ≫
            (pushoutConflation (S := ShortComplex.mk i p z) A' f).g := by simp
        _ = b ≫ pushout.inr i f ≫
            (pushoutConflation (S := ShortComplex.mk i p z) A' f).g := by
          rw [← Category.assoc, hab, Category.assoc]
        _ = 0 := by simp
    let l := hk.lift (KernelFork.ofι a ha)
    have hl : l ≫ i = a := hk.fac _ WalkingParallelPair.zero
    refine ⟨l, hl, ?_⟩
    apply (cancel_mono (pushout.inr i f)).1
    rw [Category.assoc, ← pushout.condition, ← Category.assoc, hl]
    exact hab

/-- Any pushout square of an admissible monomorphism is a pullback on the
original four arrows. No chosen ambient pushout or pullback is assumed. -/
theorem isPullback_of_inflation_isPushout {A B A' B' : C}
    {i : A ⟶ B} {f : A ⟶ A'} {g : B ⟶ B'} {j : A' ⟶ B'}
    (hi : E.inflation i) (sq : IsPushout i f g j) : IsPullback i f g j := by
  let : HasPushout i f := sq.hasPushout
  exact (E.inflation_pushout_isPullback i f hi).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) sq.isoPushout.symm
    (by simp) (by simp) (by simp) (by simp)

end CategoryTheory.ExactCategory.ExactStructure
