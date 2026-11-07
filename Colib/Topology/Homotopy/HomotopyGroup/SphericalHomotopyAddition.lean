/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.Cube.StickBreakingSkeleton
public import Colib.Topology.Homotopy.HomotopyGroup.CubicalBoundaryInduction
public import Colib.Topology.Homotopy.HomotopyGroup.SphericalSimplexQuotient

/-!
# Signed homotopy addition for actual spherical simplex faces

The genuine cubical boundary-addition theorem is transported through the
explicit stick-breaking quotient. Its lower faces give all but the final
simplex face. Its nonfinal upper faces are constant by the actual skeleton
hypothesis, and its last upper face supplies the last simplex face. The
resulting common minus sign is removed algebraically. No equality with an
arbitrarily chosen cube-to-simplex homeomorphism is asserted or required.
-/

/-! Implementation source: `Quillen/Topology/HomotopyGroups/SphericalHomotopyAddition.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Native function-subtype coordinates
and the actual ordered stick-breaking quotient are used throughout. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Topology
open scoped Topology unitInterval
universe u

namespace Topology
variable {Z : Type u} [TopologicalSpace Z] {z : Z} {n : ℕ}

/-- Pull back the full simplex through the explicitly ordered quotient. -/
def stickSimplexCube (τ : C(_root_.stdSimplex ℝ (Fin (n + 2)), Z)) :
    C((Fin (n + 1) → I), Z) := τ.comp (Cube.stickBreakingMap (n + 1))

/-- The actual geometric skeleton assumption gives exactly the basedness
needed by the genuine cubical boundary-addition theorem. -/
theorem stickSimplexCube_codimTwo (τ : C(_root_.stdSimplex ℝ (Fin (n + 2)), Z))
    (hτ : ∀ x ∈ stdSimplex.skeleton n (n + 1), τ x = z) :
    ∀ x ∈ cubeCodimTwoBoundary (Fin (n + 1)), stickSimplexCube τ x = z :=
  fun x hx ↦ hτ _ (Cube.stickBreaking_codimTwo_mem_skeleton x hx)

/-- Every lower face has literally the controlled representative of its
corresponding increasing simplex face. -/
theorem stickSimplexCube_lowerFace (τ : C(_root_.stdSimplex ℝ (Fin (n + 2)), Z))
    (hτ : ∀ x ∈ stdSimplex.skeleton n (n + 1), τ x = z) (j : Fin (n + 1)) :
    cubicalSphericalFace (stickSimplexCube τ) (stickSimplexCube_codimTwo τ hτ)
      j 0 (Or.inl rfl) = (sphericalFace τ hτ j.castSucc).toGenLoopStick := by
  ext t
  exact congrArg τ (Cube.stickBreaking_lower_face n j t)

/-- Each nonfinal upper face is literally the constant loop. -/
theorem stickSimplexCube_upperFace_const (τ : C(_root_.stdSimplex ℝ (Fin (n + 2)), Z))
    (hτ : ∀ x ∈ stdSimplex.skeleton n (n + 1), τ x = z) (j : Fin (n + 1))
    (hj : j.val < n) :
    cubicalSphericalFace (stickSimplexCube τ) (stickSimplexCube_codimTwo τ hτ)
      j 1 (Or.inr rfl) = GenLoop.const := by
  ext t
  exact hτ _ (Cube.stickBreaking_upper_mem_skeleton j hj t)

/-- The last upper face is literally the final increasing simplex face,
with no coordinate reversal or silently chosen orientation. -/
theorem stickSimplexCube_upperFace_last (τ : C(_root_.stdSimplex ℝ (Fin (n + 2)), Z))
    (hτ : ∀ x ∈ stdSimplex.skeleton n (n + 1), τ x = z) :
    cubicalSphericalFace (stickSimplexCube τ) (stickSimplexCube_codimTwo τ hτ)
      (Fin.last n) 1 (Or.inr rfl) =
        (sphericalFace τ hτ (Fin.last (n + 1))).toGenLoopStick := by
  ext t
  change τ (Cube.stickBreaking (n + 1) ((Fin.last n).insertNth 1 t)) = _
  rw [Fin.insertNth_last']
  exact congrArg τ (Cube.stickBreaking_upper_last n t)

/-- The quotient class of the controlled representative is exactly the
already established original homotopy class, not a new class map. -/
@[simp] theorem cubicalClass_toGenLoopStick (f : SphericalSimplex Z z n) :
    cubicalClass f.toGenLoopStick = f.homotopyClassStick := rfl

/-- Genuine signed simplex-face homotopy addition in the original Pi n,
for every n=m+2. The face signs are precisely the increasing-vertex signs. -/
theorem spherical_signed_homotopy_addition {m : ℕ}
    (τ : C(_root_.stdSimplex ℝ (Fin (m + 4)), Z))
    (hτ : ∀ x ∈ stdSimplex.skeleton (m + 2) (m + 3), τ x = z) :
    ∑ i : Fin (m + 4), ((-1 : ℤ) ^ i.val) •
      Additive.ofMul (sphericalFace τ hτ i).homotopyClassStick =
        (0 : Additive (HomotopyGroup.Pi (m + 2) Z z)) := by
  have h := cubical_signed_boundary_addition (stickSimplexCube τ)
    (stickSimplexCube_codimTwo τ hτ)
  have hupper (j : Fin (m + 3)) :
      Additive.ofMul (cubicalClass (cubicalSphericalFace (stickSimplexCube τ)
        (stickSimplexCube_codimTwo τ hτ) j 1 (Or.inr rfl))) =
      if j = Fin.last (m + 2) then
        Additive.ofMul (sphericalFace τ hτ (Fin.last (m + 3))).homotopyClassStick
      else 0 := by
    split_ifs with hj
    · subst j
      rw [stickSimplexCube_upperFace_last, cubicalClass_toGenLoopStick]
    · rw [stickSimplexCube_upperFace_const τ hτ j (by
        have hne : j.val ≠ m + 2 := by intro heq; exact hj (Fin.ext heq)
        omega)]
      rfl
  simp only [smul_sub, stickSimplexCube_lowerFace τ hτ, cubicalClass_toGenLoopStick, hupper,
    smul_ite, smul_zero] at h
  rw [Finset.sum_sub_distrib] at h
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Fin.val_last] at h
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  have hpow : (-1 : ℤ) ^ (m + 3) = -((-1 : ℤ) ^ (m + 2)) := by
    rw [show m + 3 = (m + 2) + 1 by omega, pow_succ, mul_neg_one]
  rw [hpow, neg_smul, ← sub_eq_zero.mp h]
  exact add_neg_cancel _

/-- Explicit four-face tetrahedral homotopy addition, including the final face. -/
theorem spherical_tetrahedral_homotopy_addition
    (τ : C(_root_.stdSimplex ℝ (Fin 4), Z))
    (hτ : ∀ x ∈ stdSimplex.skeleton 2 3, τ x = z) :
    Additive.ofMul (sphericalFace τ hτ 0).homotopyClassStick -
      Additive.ofMul (sphericalFace τ hτ 1).homotopyClassStick +
      Additive.ofMul (sphericalFace τ hτ 2).homotopyClassStick -
      Additive.ofMul (sphericalFace τ hτ 3).homotopyClassStick =
        (0 : Additive (HomotopyGroup.Pi 2 Z z)) := by
  have h := spherical_signed_homotopy_addition τ hτ
  simpa [Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using h

end Topology
