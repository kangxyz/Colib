/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.CoordinateTransposition
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Actual coordinate permutations and the time-first cubical sign

A permutation acts by the literal pullback `t ↦ p (t ∘ π)`. Its action on the
original homotopy group is proved from the genuine coordinate-transposition
homotopy, using finite permutation induction. The inverse range cycle puts
an original first time coordinate into slot `k`; its sign is `(-1)^k`.

Actual representative reparametrization also makes sense in degree zero.
Group statements require a nonempty coordinate type. Additive notation alone
does not claim commutativity; the finite signed-sum consumer uses degree ≥ 2.
-/

/-! Implementation source: `Quillen/Topology/HomotopyGroups/CoordinatePermutation.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual cubical maps,
relative homotopies, quotient multiplication, and signs are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open scoped Topology unitInterval

universe u v

namespace Topology

variable {N : Type v}
variable {X : Type u} [TopologicalSpace X] {x : X}

/-- Permuting coordinates preserves the actual cube boundary. -/
theorem cube_comp_perm_mem_boundary (π : Equiv.Perm N) (t : N → I)
    (ht : t ∈ Cube.boundary N) : t ∘ π ∈ Cube.boundary N := by
  obtain ⟨i, hi⟩ := ht
  exact ⟨π.symm i, by simpa using hi⟩

/-- Literal coordinate pullback of an original generalized loop. -/
def permuteGenLoop (π : Equiv.Perm N) (p : GenLoop N X x) : GenLoop N X x :=
  ⟨⟨fun t ↦ p (t ∘ π),
    p.val.continuous.comp (continuous_pi fun i ↦ continuous_apply (π i))⟩,
    fun t ht ↦ p.property _ (cube_comp_perm_mem_boundary π t ht)⟩

@[simp] theorem permuteGenLoop_apply (π : Equiv.Perm N) (p : GenLoop N X x)
    (t : N → I) : permuteGenLoop π p t = p (t ∘ π) := rfl

/-- The identity permutation is literally the original loop. -/
@[simp] theorem permuteGenLoop_one (p : GenLoop N X x) : permuteGenLoop 1 p = p := by
  ext t
  rfl

/-- The multiplication order matches the displayed coordinate pullback. -/
theorem permuteGenLoop_mul (π ρ : Equiv.Perm N) (p : GenLoop N X x) :
    permuteGenLoop (π * ρ) p = permuteGenLoop π (permuteGenLoop ρ p) := by
  ext t
  rfl

/-- On a zero- or one-coordinate cube every permutation acts literally trivially. -/
theorem permuteGenLoop_of_subsingleton [Subsingleton N]
    (π : Equiv.Perm N) (p : GenLoop N X x) : permuteGenLoop π p = p := by
  ext t
  change p (t ∘ π) = p t
  congr 1
  funext i
  exact congrArg t (Subsingleton.elim (π i) i)

/-- Actual boundary-relative homotopies retain their complete time coordinate
under a permutation of the cube variables. -/
def permuteGenLoopHomotopy (π : Equiv.Perm N) {p q : GenLoop N X x}
    (H : p.val.HomotopyRel q.val (Cube.boundary N)) :
    (permuteGenLoop π p).val.HomotopyRel (permuteGenLoop π q).val (Cube.boundary N) where
  toFun z := H (z.1, z.2 ∘ π)
  continuous_toFun := H.continuous.comp
    (continuous_fst.prodMk (continuous_pi fun i ↦ (continuous_apply (π i)).comp continuous_snd))
  map_zero_left t := H.apply_zero (t ∘ π)
  map_one_left t := H.apply_one (t ∘ π)
  prop' s t ht := H.eq_fst s (cube_comp_perm_mem_boundary π t ht)

/-- The original homotopy class of a generalized loop. Keeping its type head
explicit supports algebraic expressions without changing the quotient model. -/
def genLoopClass (p : GenLoop N X x) : HomotopyGroup N X x := Quotient.mk' p

/-- This class map is literally the existing homotopy quotient constructor. -/
theorem genLoopClass_eq (p : GenLoop N X x) :
    genLoopClass p = (Quotient.mk' p : HomotopyGroup N X x) := rfl

variable [DecidableEq N]

/-- A permutation by a swap is the existing geometric coordinate transposition. -/
theorem permuteGenLoop_swap (i j : N) (hij : i ≠ j) (p : GenLoop N X x) :
    permuteGenLoop (Equiv.swap i j) p = transposeGenLoop i j hij p := by
  ext t
  change p (t ∘ Equiv.swap i j) = p (cubeCoordinateSwap i j t)
  congr 1
  funext k
  simp only [Function.comp_apply, Equiv.swap_apply_def, cubeCoordinateSwap]
  split_ifs <;> rfl

/-- The sign of a finite coordinate permutation acts on the actual homotopy
class by the corresponding integer power, proved from actual transpositions. -/
theorem permuteGenLoop_class [Fintype N] [Nonempty N]
    (π : Equiv.Perm N) (p : GenLoop N X x) :
    genLoopClass (permuteGenLoop π p) = genLoopClass p ^ (π.sign : ℤ) := by
  induction π using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul π i j hij ih =>
    rw [permuteGenLoop_mul, permuteGenLoop_swap i j hij]
    have hswap : genLoopClass (transposeGenLoop i j hij (permuteGenLoop π p)) =
        (genLoopClass (permuteGenLoop π p))⁻¹ := transposeGenLoop_class i j hij _
    rw [hswap, ih]
    simp [Equiv.Perm.sign_swap hij, zpow_neg]

/-- Additive notation for the same proved sign action. This uses no reordering
of terms, and therefore does not assume a commutative homotopy group. -/
theorem permuteGenLoop_additiveClass [Fintype N] [Nonempty N]
    (π : Equiv.Perm N) (p : GenLoop N X x) :
    Additive.ofMul (genLoopClass (permuteGenLoop π p)) =
      (π.sign : ℤ) • Additive.ofMul (genLoopClass p) := by
  rw [permuteGenLoop_class, ofMul_zpow]

/-- The inverse range cycle gives the literal time-first coordinate insertion,
with every remaining coordinate still in increasing order. -/
theorem permuteGenLoop_cycleRange_symm_apply {n : ℕ} (k : Fin (n + 1))
    (p : GenLoop (Fin (n + 1)) X x) (t : Fin (n + 1) → I) :
    permuteGenLoop k.cycleRange.symm p t = p (Fin.cons (t k) (k.removeNth t)) := by
  rw [permuteGenLoop_apply, Fin.cons_removeNth_eq_comp_cycleRange_symm]

/-- Moving the first time coordinate to slot `k` has sign `(-1)^k`, in the
original multiplicative homotopy group. -/
theorem permuteGenLoop_cycleRange_symm_class {n : ℕ} (k : Fin (n + 1))
    (p : GenLoop (Fin (n + 1)) X x) :
    genLoopClass (permuteGenLoop k.cycleRange.symm p) =
      genLoopClass p ^ ((-1 : ℤ) ^ k.val) := by
  simpa using permuteGenLoop_class k.cycleRange.symm p

/-- The explicit time-first permutation contributes `(-1)^k` in additive
notation, including the harmless degree-one identity case. -/
theorem permuteGenLoop_cycleRange_symm_additiveClass {n : ℕ} (k : Fin (n + 1))
    (p : GenLoop (Fin (n + 1)) X x) :
    Additive.ofMul (genLoopClass (permuteGenLoop k.cycleRange.symm p)) =
      ((-1 : ℤ) ^ k.val) • Additive.ofMul (genLoopClass p) := by
  rw [permuteGenLoop_cycleRange_symm_class, ofMul_zpow]

end Topology
