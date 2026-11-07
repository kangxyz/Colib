/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Resolution.PresentationIndependence
public import Colib.CategoryTheory.ExactCategory.Resolution.LengthStrata
public import Colib.CategoryTheory.ExactCategory.Composition

/-! Extracted from `Quillen/Aglib/CategoryTheory/ExactCategory/Resolution/Strata.lean`.
Pinned Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd and
Aglib 2c34f185fa859e862661f939cd216b07bcccfb26.
Actual maps and assumptions are retained; no Resolution K-equivalence is claimed. -/

/-!
# Resolving closure of finite-resolution-length strata

All arguments use actual admissible pullbacks and the kernel sequences of
composite admissible epimorphisms. No projectivity or lifting of comparison
maps is assumed. Global finite resolutions supply the required covers.
-/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (P Q : ObjectProperty C)
  [Q.IsClosedUnderIsomorphisms] [E.IsExtensionClosed Q] [E.IsKernelClosed Q]

omit [Q.IsClosedUnderIsomorphisms] [E.IsKernelClosed Q] in
/-- Quotienting a once-presented object by a `Q`-subobject is again once
presented: the new syzygy is an extension of two `Q`-objects. -/
lemma resolutionStep_of_conflation {S : ShortComplex C}
    (hS : E.conflation S) (hA : Q S.X₁) (hB : E.ResolutionStep P Q S.X₂) :
    E.ResolutionStep P Q S.X₃ := by
  obtain ⟨T⟩ := hB
  let : HasPullback T.g S.f := E.deflation.hasPullback S.f T.deflation
  have hPB : Q (pullback T.g S.f) := E.prop_pullback Q T.conflation T.syzygy_mem hA S.f
  exact ⟨⟨pullback T.g S.f, T.middle, pullback.fst _ _, T.g ≫ S.g,
    by rw [← Category.assoc, pullback.condition, Category.assoc, S.zero, comp_zero],
    E.composite_deflation_conflation T.conflation hS, T.middle_mem, hPB⟩⟩

/-- One-step closure is closed under kernels once each previous-stratum object
itself has a one-step presentation. -/
theorem resolutionStep_kernelClosed (hPQ : P ≤ Q) (hQ : Q ≤ E.ResolutionStep P Q) :
    E.IsKernelClosed (E.ResolutionStep P Q) where
  prop_kernel {S} hS hB hC := by
    obtain ⟨T⟩ := hB
    let : HasPullback T.g S.f := E.deflation.hasPullback S.f T.deflation
    have hcomp := E.composite_deflation_conflation T.conflation hS
    have hPB : Q (pullback T.g S.f) :=
      E.kernel_mem_of_resolutionStep P Q hPQ hcomp (hPQ _ T.middle_mem) hC
    exact E.resolutionStep_of_conflation P Q
      (E.pullbackConflation_mem T.conflation S.f) T.syzygy_mem (hQ _ hPB)

/-- The mixed extension case with a resolving quotient. Choosing an actual
cover and comparing its two kernel sequences avoids any projective lift. -/
lemma resolutionStep_extension_by_mem (hPQ : P ≤ Q)
    (h : E.ResolutionHypothesis P) {S : ShortComplex C} (hS : E.conflation S)
    (hA : E.ResolutionStep P Q S.X₁) (hC : P S.X₃) :
    E.ResolutionStep P Q S.X₂ := by
  obtain ⟨R⟩ := h S.X₂
  obtain ⟨Y, p, hY, hp⟩ := R.presentation
  obtain ⟨K, i, hi, hT⟩ := hp
  let : HasPullback p S.f := E.deflation.hasPullback S.f (E.deflation_of_conflation hT)
  have hcomp := E.composite_deflation_conflation hT hS
  have hPB : Q (pullback p S.f) :=
    IsKernelClosed.prop_kernel (E := E) (P := Q) hcomp (hPQ _ hY) (hPQ _ hC)
  have hK : Q K := E.kernel_mem_of_resolutionStep P Q hPQ
    (E.pullbackConflation_mem hT S.f) hPB hA
  exact ⟨⟨K, Y, i, p, hi, hT, hY, hK⟩⟩

omit [Q.IsClosedUnderIsomorphisms] [E.IsExtensionClosed Q] [E.IsKernelClosed Q] in
/-- Symmetric form of base change, with the first pullback projection as its
admissible epimorphism. -/
lemma pullbackConflationLeft_mem {S : ShortComplex C} (hS : E.conflation S)
    {T : C} (g : T ⟶ S.X₃) [HasPullback g S.g] :
    E.conflation (ShortComplex.mk
      (pullback.lift (f := g) (g := S.g) 0 S.f (by simp))
      (pullback.fst g S.g) (by simp)) := by
  let : HasPullback S.g g := hasPullback_symmetry _ _
  let U := pullbackConflation (S := S) T g
  let V := ShortComplex.mk
    (pullback.lift (f := g) (g := S.g) 0 S.f (by simp))
    (pullback.fst g S.g) (by simp)
  change E.conflation V
  apply E.iso_closed (S := U) (T := V)
    (ShortComplex.isoMk (Iso.refl _) (pullbackSymmetry S.g g) (Iso.refl _) ?_ ?_)
    (E.pullbackConflation_mem hS g)
  · apply pullback.hom_ext <;> simp [U, V]
  · simp [U, V]

/-- One-step resolution closure is extension closed. Pullback resolves the
quotient first; the mixed case resolves the resulting extension, and composing
those two admissible epimorphisms gives the requested resolution. -/
theorem resolutionStep_extensionClosed (hPQ : P ≤ Q)
    (h : E.ResolutionHypothesis P) : E.IsExtensionClosed (E.ResolutionStep P Q) where
  prop_middle {S} hS hA hC := by
    obtain ⟨T⟩ := hC
    let : HasPullback S.g T.g := E.deflation.hasPullback T.g (E.deflation_of_conflation hS)
    have hPB : E.ResolutionStep P Q (pullback S.g T.g) :=
      E.resolutionStep_extension_by_mem P Q hPQ h
        (E.pullbackConflation_mem hS T.g) hA T.middle_mem
    exact E.resolutionStep_of_conflation P Q
      (E.pullbackConflationLeft_mem T.conflation S.g) T.syzygy_mem hPB

end CategoryTheory.ExactCategory.ExactStructure

namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (P : ObjectProperty C)
  [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
section LengthStrata

/-- Under the actual global finite-resolution hypothesis, every length stratum
is resolving. This is simultaneous induction using presentation independence,
not a projective horseshoe lemma. -/
theorem resolutionLength_resolving [E.IsExtensionClosed P] [E.IsKernelClosed P]
    (h : E.ResolutionHypothesis P) (n : ℕ) :
    E.IsExtensionClosed (E.ResolutionLength P n) ∧ E.IsKernelClosed (E.ResolutionLength P n) := by
  induction n with
  | zero =>
    have he : E.ResolutionLength P 0 = P := by
      funext X
      exact propext (E.resolutionLength_zero_iff P X)
    rw [he]
    exact ⟨inferInstance, inferInstance⟩
  | succ n ih =>
    let := ih.1
    let := ih.2
    have hQ : E.ResolutionLength P n ≤ E.ResolutionStep P (E.ResolutionLength P n) := by
      intro X hX
      exact (E.resolutionLength_succ_iff P n X).1
        (E.resolutionLength_mono P (Nat.le_succ n) _ hX)
    rw [E.resolutionLength_succ_eq P n]
    exact ⟨E.resolutionStep_extensionClosed P (E.ResolutionLength P n)
      (E.le_resolutionLength P n) h,
      E.resolutionStep_kernelClosed P (E.ResolutionLength P n)
        (E.le_resolutionLength P n) hQ⟩

/-- Typeclass access to the proved extension closure of each length stratum. -/
instance resolutionLength_extensionClosed [E.IsExtensionClosed P] [E.IsKernelClosed P]
    [h : Fact (E.ResolutionHypothesis P)] (n : ℕ) :
    E.IsExtensionClosed (E.ResolutionLength P n) := (E.resolutionLength_resolving P h.out n).1

/-- Typeclass access to the proved kernel closure of each length stratum. -/
instance resolutionLength_kernelClosed [E.IsExtensionClosed P] [E.IsKernelClosed P]
    [h : Fact (E.ResolutionHypothesis P)] (n : ℕ) :
    E.IsKernelClosed (E.ResolutionLength P n) := (E.resolutionLength_resolving P h.out n).2

/-- Finite biproduct closure is derived from extension closure and zero. -/
instance resolutionLength_finiteProducts [E.IsExtensionClosed P] [E.IsKernelClosed P]
    [Fact (E.ResolutionHypothesis P)] (n : ℕ) :
    (E.ResolutionLength P n).IsClosedUnderFiniteProducts :=
  E.extensionClosed_finiteProducts (E.ResolutionLength P n)

end LengthStrata
end CategoryTheory.ExactCategory.ExactStructure
