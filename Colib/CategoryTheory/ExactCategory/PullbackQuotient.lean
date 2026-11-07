/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Functor.Pullbacks



/-!
# Actual kernels and quotients under admissible pullback

The pullback of an actual kernel computes the kernel of the composite. Under
an admissible epimorphism this gives the original conflation with the same
actual quotient, retaining its maps and exact-category hypotheses.
-/
/- Adapted from the corresponding Quillen Q/S reconstruction source at
   c561118b7795eb9780be9ed391c3251d6a4d0afd. Native Colib objects are retained. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe v u

namespace CategoryTheory.ExactCategory.ExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : CategoryTheory.ExactCategory.ExactStructure C)

/-- A pullback of an actual kernel computes the kernel of the composite. -/
def pullbackKernelComposite {P A B K Q : C} {a : K ⟶ P} {v : K ⟶ A}
    {p : P ⟶ B} {i : A ⟶ B} {q : B ⟶ Q}
    (sq : IsPullback a v p i) (w : i ≫ q = 0)
    (hi : IsLimit (KernelFork.ofι i w)) :
    IsLimit (KernelFork.ofι a (show a ≫ (p ≫ q) = 0 from by
      rw [← Category.assoc, sq.w, Category.assoc, w, comp_zero])) := by
  refine KernelFork.IsLimit.ofι _ _
    (fun {W} f hf ↦ sq.lift f (hi.lift (KernelFork.ofι (f ≫ p) (by simpa [Category.assoc] using
      hf)))
      (by symm; exact hi.fac _ WalkingParallelPair.zero)) ?_ ?_
  · intro W f hf
    exact sq.lift_fst _ _ _
  · intro W f hf m hm
    apply sq.hom_ext
    · simpa using hm
    · apply (Fork.IsLimit.hom_ext hi)
      change (m ≫ v) ≫ i = _
      rw [Category.assoc, ← sq.w, ← Category.assoc, hm, sq.lift_snd]
      symm
      exact hi.fac _ WalkingParallelPair.zero

/-- A pullback of an admissible inclusion against a deflation has the same
actual quotient as the original inclusion. -/
theorem pullback_conflation_same_quotient {P A B K Q : C} {a : K ⟶ P} {v : K ⟶ A}
    {p : P ⟶ B} {i : A ⟶ B} {q : B ⟶ Q}
    (sq : IsPullback a v p i) (w : i ≫ q = 0)
    (hc : E.conflation (ShortComplex.mk i q w)) (hp : E.deflation p) :
    E.conflation (ShortComplex.mk a (p ≫ q) (show a ≫ (p ≫ q) = 0 from by
      rw [← Category.assoc, sq.w, Category.assoc, w, comp_zero])) :=
  E.conflation_of_isKernel _ (pullbackKernelComposite sq w (E.kernel _ hc))
    (E.deflation_comp p q hp (E.deflation_of_conflation hc))

end CategoryTheory.ExactCategory.ExactStructure
