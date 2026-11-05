/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.CategoryTheory.ExactCategory.Basic

/-!
# Exact kernels and their pullback squares

The actual kernel of an admissible quotient belongs to its conflation. A pullback
of such a quotient retains the original kernel object. The kernel universal
property also supplies its square against zero as an actual pullback.

## Implementation provenance

Adapted from `Quillen/Aglib/CategoryTheory/ExactCategory/KernelPullback.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining all three
statements, universal-property proofs and independent object/hom universes.
The unused `Mathlib.CategoryTheory.SingleObj` import is omitted.
-/

@[expose] public noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- Any chosen kernel of an admissible quotient belongs to its conflation. -/
lemma conflation_of_deflation_of_isKernel {S : ShortComplex C}
    (hg : E.deflation S.g) (hf : IsLimit (KernelFork.ofι S.f S.zero)) :
    E.conflation S := by
  obtain ⟨K, i, hi, hT⟩ := hg
  let hTf := E.kernel (ShortComplex.mk i S.g hi) hT
  let e := hTf.conePointUniqueUpToIso hf
  let eS : ShortComplex.mk i S.g hi ≅ S :=
    ShortComplex.isoMk e (Iso.refl _) (Iso.refl _) (by
      simpa using hTf.conePointUniqueUpToIso_hom_comp hf WalkingParallelPair.zero) (by simp)
  exact E.iso_closed eS hT

/-- Pulling back an admissible quotient gives a conflation with the same
kernel object, using the genuine pullback universal property. -/
lemma conflation_pullback_same_kernel {S : ShortComplex C} (hS : E.conflation S)
    {A P : C} {a : P ⟶ A} {b : P ⟶ S.X₂} {i : A ⟶ S.X₃}
    (sq : IsPullback a b i S.g) :
    E.conflation (ShortComplex.mk (sq.lift 0 S.f (by simp [S.zero])) a (by simp)) := by
  let k := sq.lift 0 S.f (by simp [S.zero])
  have hk : k ≫ a = 0 := by simp [k]
  have ha : E.deflation a := E.deflation.of_isPullback sq.flip (E.deflation_of_conflation hS)
  apply E.conflation_of_deflation_of_isKernel ha
  refine KernelFork.IsLimit.ofι k hk
    (fun {W} g hg => (E.kernel S hS).lift
      (KernelFork.ofι (g ≫ b) (by rw [Category.assoc, ← sq.w, ← Category.assoc, hg]; simp)))
    ?_ ?_
  · intro W g hg
    apply sq.hom_ext
    · simp [Category.assoc, k, hg]
    · simpa [k] using (E.kernel S hS).fac
        (KernelFork.ofι (g ≫ b)
          (by rw [Category.assoc, ← sq.w, ← Category.assoc, hg]; simp))
        WalkingParallelPair.zero
  · intro W g hg m hm
    apply Fork.IsLimit.hom_ext (E.kernel S hS)
    have hmk : m ≫ k ≫ b = g ≫ b := by rw [← Category.assoc, hm]
    simpa [k] using hmk.trans
      ((E.kernel S hS).fac
        (KernelFork.ofι (g ≫ b)
          (by rw [Category.assoc, ← sq.w, ← Category.assoc, hg]; simp))
          WalkingParallelPair.zero).symm

open scoped ZeroObject

/-- The kernel universal property gives the pullback square against zero. -/
lemma conflation_kernel_isPullback {S : ShortComplex C} (hS : E.conflation S) :
    IsPullback (0 : S.X₁ ⟶ 0) S.f (0 : 0 ⟶ S.X₃) S.g := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (by simp [S.zero])
    (fun s => (E.kernel S hS).lift
      (KernelFork.ofι s.snd (by rw [← s.condition]; simp))) ?_ ?_ ?_)
  · intro s
    exact Subsingleton.elim _ _
  · intro s
    exact Fork.IsLimit.lift_ι _
  · intro s m hm hn
    apply Fork.IsLimit.hom_ext (E.kernel S hS)
    apply hn.trans
    simpa using ((E.kernel S hS).fac
      (KernelFork.ofι s.snd (by rw [← s.condition]; simp)) WalkingParallelPair.zero).symm

end CategoryTheory.ExactCategory.ExactStructure

attribute [colib_tag "COL-0074",
  colib_ref "BuhlerExactCategories" "Proposition 2.12, dual of (i) implies (iv)" "adaptation"
    "Pullback of a conflation along its quotient map retains the original kernel object"]
  CategoryTheory.ExactCategory.ExactStructure.conflation_pullback_same_kernel

attribute [colib_tag "COL-0074",
  colib_ref "BuhlerExactCategories" "Definition 2.1, kernel-cokernel pairs and isomorphism closure"
    "ingredient" "Specified kernel universal properties, not existence of arbitrary kernels"]
  CategoryTheory.ExactCategory.ExactStructure.conflation_of_deflation_of_isKernel
  CategoryTheory.ExactCategory.ExactStructure.conflation_kernel_isPullback
