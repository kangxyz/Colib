/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, kangxyz
-/
module

public import Colib.LinearAlgebra.Matrix.Bruhat.RootUpdate
public import Colib.LinearAlgebra.Matrix.Bruhat.Coordinates
public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.Stabilization
public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary
public import Colib.LinearAlgebra.Matrix.Bruhat.Decomposition

/-!
# Opposite

Finite matrix Bruhat opposite over fields, using the native general linear
group, with the original rank hypotheses and signed matrix formulas.

## Implementation provenance

Adapted from `Quillen/Aglib/LinearAlgebra/Matrix/Bruhat/Opposite.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Native elementary matrix units and
finite matrix stabilization are used directly.
-/

@[expose] public section

/-! ## OppositePivot -/

section

noncomputable section
universe u
namespace Matrix.Bruhat
variable (F : Type u) [Field F]

lemma matrixMonomial_val {n : ℕ} (m : MonomialGroup F n) (r s : Fin n) :
    (monomialToGL F n m).val r s = if r = m.right s then (m.left r : F) else 0 := rfl

lemma rootW_mul_val {n : ℕ} (i j : Fin n) (hij : i ≠ j) (a : Fˣ)
    (g : Matrix.GeneralLinearGroup (Fin n) F) (r s : Fin n) :
    (monomialToGL F n (rootWMonomial F i j a) * g).val r s =
      if r = i then (a : F) * g.val j s else
      if r = j then -((a⁻¹ : Fˣ) : F) * g.val i s else g.val r s := by
  change (monomialMatrix F (rootWMonomial F i j a) * g.val) r s = _
  rw [monomial_mul_matrix]
  by_cases hri : r = i <;> by_cases hrj : r = j <;>
    simp_all [rootWMonomial, Pi.mulSingle_apply, Equiv.swap_apply_def, eq_comm]

lemma mul_rootW_val {n : ℕ} (i j : Fin n) (hij : i ≠ j) (a : Fˣ)
    (g : Matrix.GeneralLinearGroup (Fin n) F) (r s : Fin n) :
    (g * monomialToGL F n (rootWMonomial F i j a)).val r s =
      if s = i then -((a⁻¹ : Fˣ) : F) * g.val r j else
      if s = j then (a : F) * g.val r i else g.val r s := by
  change (g.val * monomialMatrix F (rootWMonomial F i j a)) r s = _
  rw [matrix_mul_monomial]
  by_cases hsi : s = i <;> by_cases hsj : s = j <;>
    simp_all [rootWMonomial, Pi.mulSingle_apply, Equiv.swap_apply_def, eq_comm, mul_comm]

lemma rootH_mul_val {n : ℕ} (i j : Fin n) (hij : i ≠ j) (a : Fˣ)
    (g : Matrix.GeneralLinearGroup (Fin n) F) (r s : Fin n) :
    (monomialToGL F n (rootHMonomial F i j a) * g).val r s =
      if r = i then (a : F) * g.val r s else
      if r = j then ((a⁻¹ : Fˣ) : F) * g.val r s else g.val r s := by
  change (monomialMatrix F (rootHMonomial F i j a) * g.val) r s = _
  rw [monomial_mul_matrix]
  change ((Pi.mulSingle i a * Pi.mulSingle j a⁻¹ : Fin n → Fˣ) r : F) * g.val r s = _
  by_cases hri : r = i <;> by_cases hrj : r = j <;>
    simp_all [Pi.mulSingle_apply, eq_comm]

lemma mul_rootH_val {n : ℕ} (i j : Fin n) (hij : i ≠ j) (a : Fˣ)
    (g : Matrix.GeneralLinearGroup (Fin n) F) (r s : Fin n) :
    (g * monomialToGL F n (rootHMonomial F i j a)).val r s =
      if s = i then (a : F) * g.val r s else
      if s = j then ((a⁻¹ : Fˣ) : F) * g.val r s else g.val r s := by
  change (g.val * monomialMatrix F (rootHMonomial F i j a)) r s = _
  rw [matrix_mul_monomial]
  change g.val r s * ((Pi.mulSingle i a * Pi.mulSingle j a⁻¹ : Fin n → Fˣ) s : F) = _
  by_cases hsi : s = i <;> by_cases hsj : s = j <;>
    simp_all [Pi.mulSingle_apply, eq_comm, mul_comm]

/-- The left intermediate pivot is `u`, and the new right entry is `v-f/u`. -/
lemma opposite_left_factorization_nonzero {n : ℕ}
    (m : MonomialGroup F n) (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (hk : m.right k = j) (hl : m.right l = i)
    (u f : Fˣ) (v : F) (hf : m.left i = -f * m.left j) :
    monomialToGL F n (rootWMonomial F i j 1) *
        Matrix.GeneralLinearGroup.elementary i j hij (u : F) * monomialToGL F n m *
        Matrix.GeneralLinearGroup.elementary k l hkl v =
      Matrix.GeneralLinearGroup.elementary i j hij (-((u⁻¹ : Fˣ) : F)) *
        monomialToGL F n (rootHMonomial F i j (-u⁻¹) * m) *
        Matrix.GeneralLinearGroup.elementary k l hkl (v - (f : F) / (u : F)) := by
  have hf' : (m.left i : F) = -(f : F) * (m.left j : F) := by
    simpa only [Units.val_mul, Units.val_neg] using
      congrArg (fun z : Fˣ => (z : F)) hf
  have hpi (s : Fin n) : i = m.right s ↔ s = l := by
    rw [← hl, m.right.injective.eq_iff, eq_comm]
  have hpj (s : Fin n) : j = m.right s ↔ s = k := by
    rw [← hk, m.right.injective.eq_iff, eq_comm]
  rw [mul_assoc (monomialToGL F n (rootWMonomial F i j 1))
    (Matrix.GeneralLinearGroup.elementary i j hij (u : F)) (monomialToGL F n m)]
  apply Units.ext
  ext r s
  rw [map_mul]
  simp only [rootW_mul_val F i j hij, elementary_mul_val, mul_elementary_val,
    rootH_mul_val F i j hij, matrixMonomial_val]
  by_cases hri : r = i <;> by_cases hrj : r = j <;>
    by_cases hsk : s = k <;> by_cases hsl : s = l <;>
      simp [hri, hrj, hsk, hsl, hij, hij.symm, hkl,
        hpi, hpj, hk, hl, hf', Units.val_inv_eq_inv_val]
  all_goals field_simp
  all_goals ring

/-- The right intermediate pivot is `v`, and the new left entry is `u-f/v`. -/
lemma opposite_right_factorization_nonzero {n : ℕ}
    (m : MonomialGroup F n) (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (hk : m.right k = j) (hl : m.right l = i)
    (u : F) (v f : Fˣ) (hf : m.left i = -f * m.left j) :
    Matrix.GeneralLinearGroup.elementary i j hij u * monomialToGL F n m *
        Matrix.GeneralLinearGroup.elementary k l hkl (v : F) *
        monomialToGL F n (rootWMonomial F k l (-1)) =
      Matrix.GeneralLinearGroup.elementary i j hij (u - (f : F) / (v : F)) *
        monomialToGL F n (m * rootHMonomial F k l v) *
        Matrix.GeneralLinearGroup.elementary k l hkl (-((v⁻¹ : Fˣ) : F)) := by
  have hf' : (m.left i : F) = -(f : F) * (m.left j : F) := by
    simpa only [Units.val_mul, Units.val_neg] using
      congrArg (fun z : Fˣ => (z : F)) hf
  have hpi (s : Fin n) : i = m.right s ↔ s = l := by
    rw [← hl, m.right.injective.eq_iff, eq_comm]
  have hpj (s : Fin n) : j = m.right s ↔ s = k := by
    rw [← hk, m.right.injective.eq_iff, eq_comm]
  apply Units.ext
  ext r s
  rw [map_mul]
  simp only [mul_rootW_val F k l hkl, elementary_mul_val, mul_elementary_val,
    mul_rootH_val F k l hkl, matrixMonomial_val]
  by_cases hri : r = i <;> by_cases hrj : r = j <;>
    by_cases hsk : s = k <;> by_cases hsl : s = l <;>
      simp [hri, hrj, hsk, hsl, hij, hij.symm, hkl, hkl.symm,
        hpi, hpj, hk, hl, hf', Units.val_inv_eq_inv_val]
  all_goals field_simp
  all_goals ring

/-- Opposite transported roots, with the actual signed matrix coefficient retained. -/
lemma opposite_crossing_factorization_nonzero {n : ℕ}
    (m : MonomialGroup F n) (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (hk : m.right k = j) (hl : m.right l = i)
    (u v : F) (f d : Fˣ) (hf : m.left i = -f * m.left j)
    (hd : (d : F) = u * v - (f : F)) :
    monomialToGL F n (rootWMonomial F i j 1) *
        Matrix.GeneralLinearGroup.elementary i j hij u * monomialToGL F n m *
        Matrix.GeneralLinearGroup.elementary k l hkl v *
        monomialToGL F n (rootWMonomial F k l (-1)) =
      Matrix.GeneralLinearGroup.elementary i j hij (-v / (d : F)) *
        monomialToGL F n (rootHMonomial F i j (-d⁻¹) * m) *
        Matrix.GeneralLinearGroup.elementary k l hkl (-u / (d : F)) := by
  have hf' : (m.left i : F) = -(f : F) * (m.left j : F) := by
    simpa only [Units.val_mul, Units.val_neg] using
      congrArg (fun z : Fˣ => (z : F)) hf
  have hpi (s : Fin n) : i = m.right s ↔ s = l := by
    rw [← hl, m.right.injective.eq_iff, eq_comm]
  have hpj (s : Fin n) : j = m.right s ↔ s = k := by
    rw [← hk, m.right.injective.eq_iff, eq_comm]
  rw [mul_assoc (monomialToGL F n (rootWMonomial F i j 1))
    (Matrix.GeneralLinearGroup.elementary i j hij u) (monomialToGL F n m)]
  apply Units.ext
  ext r s
  rw [map_mul]
  simp only [mul_rootW_val F k l hkl, rootW_mul_val F i j hij,
    elementary_mul_val, mul_elementary_val, rootH_mul_val F i j hij, matrixMonomial_val]
  by_cases hri : r = i <;> by_cases hrj : r = j <;>
    by_cases hsk : s = k <;> by_cases hsl : s = l <;>
      simp [hri, hrj, hsk, hsl, hij, hij.symm, hkl, hkl.symm,
        hpi, hpj, hk, hl, hf', Units.val_inv_eq_inv_val]
  all_goals field_simp
  all_goals rw [hd]
  all_goals ring

/-- At the vanishing denominator the diagonal branch becomes a Weyl branch. -/
lemma opposite_crossing_factorization_zero {n : ℕ}
    (m : MonomialGroup F n) (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (hk : m.right k = j) (hl : m.right l = i)
    (u v f : Fˣ) (hf : m.left i = -f * m.left j)
    (hzero : (u : F) * (v : F) = (f : F)) :
    monomialToGL F n (rootWMonomial F i j 1) *
        Matrix.GeneralLinearGroup.elementary i j hij (u : F) * monomialToGL F n m *
        Matrix.GeneralLinearGroup.elementary k l hkl (v : F) *
        monomialToGL F n (rootWMonomial F k l (-1)) =
      Matrix.GeneralLinearGroup.elementary i j hij (-((u⁻¹ : Fˣ) : F)) *
        monomialToGL F n (rootWMonomial F i j v * m) := by
  have hf' : (m.left i : F) = -(f : F) * (m.left j : F) := by
    simpa only [Units.val_mul, Units.val_neg] using
      congrArg (fun z : Fˣ => (z : F)) hf
  have hpi (s : Fin n) : i = m.right s ↔ s = l := by
    rw [← hl, m.right.injective.eq_iff, eq_comm]
  have hpj (s : Fin n) : j = m.right s ↔ s = k := by
    rw [← hk, m.right.injective.eq_iff, eq_comm]
  rw [mul_assoc (monomialToGL F n (rootWMonomial F i j 1))
    (Matrix.GeneralLinearGroup.elementary i j hij (u : F)) (monomialToGL F n m)]
  apply Units.ext
  ext r s
  rw [map_mul]
  simp only [mul_rootW_val F k l hkl, rootW_mul_val F i j hij,
    elementary_mul_val, mul_elementary_val, matrixMonomial_val]
  by_cases hri : r = i <;> by_cases hrj : r = j <;>
    by_cases hsk : s = k <;> by_cases hsl : s = l <;>
      simp [hri, hrj, hsk, hsl, hij, hij.symm, hkl, hkl.symm,
        hpi, hpj, hk, hl, hf', Units.val_inv_eq_inv_val]
  all_goals field_simp
  all_goals rw [← hzero]
  all_goals ring

/-- A zero crossing denominator cannot occur at a zero input parameter. -/
lemma opposite_crossing_zero_parameters (u v : F) (f : Fˣ)
    (hzero : u * v - (f : F) = 0) : u ≠ 0 ∧ v ≠ 0 := by
  have huv : u * v = (f : F) := sub_eq_zero.mp hzero
  exact mul_ne_zero_iff.mp (huv ▸ f.ne_zero)

/-- The uniform nonzero-denominator formula includes either zero input parameter. -/
lemma opposite_crossing_denominator_of_zero_parameter (u v : F) (f : Fˣ)
    (hz : u = 0 ∨ v = 0) : u * v - (f : F) = -(f : F) ∧
      u * v - (f : F) ≠ 0 := by
  rcases hz with rfl | rfl <;> simp [f.ne_zero]

end Matrix.Bruhat

end

end

/-! ## OppositeBruhat -/

section

noncomputable section
universe u
namespace Matrix.Bruhat
variable (F : Type u) [Field F]

/-- The signed coefficient is determined by the actual two monomial rows. -/
def oppositeRootCoefficient {n : ℕ} (m : MonomialGroup F n) (i j : Fin n) : Fˣ :=
  -m.left i * (m.left j)⁻¹

lemma oppositeRootCoefficient_spec {n : ℕ} (m : MonomialGroup F n) (i j : Fin n) :
    m.left i = -oppositeRootCoefficient F m i j * m.left j := by
  simp [oppositeRootCoefficient, mul_assoc]

/-- The actual two upper simple-root factors surrounding a finite monomial matrix. -/
def simpleBruhatRepresentative (n : ℕ) (i k : Fin n) (m : MonomialGroup F (n + 1))
    (u v : F) : Matrix.GeneralLinearGroup (Fin (n + 1)) F :=
  Matrix.GeneralLinearGroup.elementary i.castSucc i.succ i.castSucc_lt_succ.ne u *
    monomialToGL F (n + 1) m *
    Matrix.GeneralLinearGroup.elementary k.castSucc k.succ k.castSucc_lt_succ.ne v

lemma simpleBruhatRepresentative_projection (n : ℕ) (i k : Fin n)
    (m : MonomialGroup F (n + 1)) (u v : F) :
    bruhatMonomial F (n + 1) (simpleBruhatRepresentative F n i k m u v) = m := by
  apply bruhatMonomial_eq_of_factorization F (n + 1) _ m
    (simpleUpper F n i u) (simpleUpper F n k v)
  rfl

theorem opposite_left_bruhat_nonzero (n : ℕ) (i k : Fin n)
    (m : MonomialGroup F (n + 1))
    (hk : m.right k.castSucc = i.succ) (hl : m.right k.succ = i.castSucc)
    (u : Fˣ) (v : F) :
    bruhatMonomial F (n + 1)
      (monomialToGL F (n + 1) (rootWMonomial F i.castSucc i.succ 1) *
        simpleBruhatRepresentative F n i k m (u : F) v) =
      rootHMonomial F i.castSucc i.succ (-u⁻¹) * m := by
  apply bruhatMonomial_eq_of_factorization F (n + 1) _ _
    (simpleUpper F n i (-((u⁻¹ : Fˣ) : F)))
    (simpleUpper F n k (v - (oppositeRootCoefficient F m i.castSucc i.succ : F) / (u : F)))
  simpa only [simpleBruhatRepresentative, simpleUpper, mul_assoc] using
    opposite_left_factorization_nonzero F m i.castSucc i.succ k.castSucc k.succ
      i.castSucc_lt_succ.ne k.castSucc_lt_succ.ne hk hl u
      (oppositeRootCoefficient F m i.castSucc i.succ) v
      (oppositeRootCoefficient_spec F m i.castSucc i.succ)

theorem opposite_right_bruhat_nonzero (n : ℕ) (i k : Fin n)
    (m : MonomialGroup F (n + 1))
    (hk : m.right k.castSucc = i.succ) (hl : m.right k.succ = i.castSucc)
    (u : F) (v : Fˣ) :
    bruhatMonomial F (n + 1)
      (simpleBruhatRepresentative F n i k m u (v : F) *
        monomialToGL F (n + 1) (rootWMonomial F k.castSucc k.succ (-1))) =
      m * rootHMonomial F k.castSucc k.succ v := by
  apply bruhatMonomial_eq_of_factorization F (n + 1) _ _
    (simpleUpper F n i (u - (oppositeRootCoefficient F m i.castSucc i.succ : F) / (v : F)))
    (simpleUpper F n k (-((v⁻¹ : Fˣ) : F)))
  exact opposite_right_factorization_nonzero F m i.castSucc i.succ k.castSucc k.succ
    i.castSucc_lt_succ.ne k.castSucc_lt_succ.ne hk hl u v
    (oppositeRootCoefficient F m i.castSucc i.succ)
    (oppositeRootCoefficient_spec F m i.castSucc i.succ)

theorem simple_left_bruhat_zero (n : ℕ) (i k : Fin n)
    (m : MonomialGroup F (n + 1)) (v : F) :
    bruhatMonomial F (n + 1)
      (monomialToGL F (n + 1) (rootWMonomial F i.castSucc i.succ 1) *
        simpleBruhatRepresentative F n i k m 0 v) =
      rootWMonomial F i.castSucc i.succ 1 * m := by
  apply bruhatMonomial_eq_of_factorization F (n + 1) _ _ 1 (simpleUpper F n k v)
  simp [simpleBruhatRepresentative, simpleUpper, mul_assoc]

theorem simple_right_bruhat_zero (n : ℕ) (i k : Fin n)
    (m : MonomialGroup F (n + 1)) (u : F) :
    bruhatMonomial F (n + 1)
      (simpleBruhatRepresentative F n i k m u 0 *
        monomialToGL F (n + 1) (rootWMonomial F k.castSucc k.succ (-1))) =
      m * rootWMonomial F k.castSucc k.succ (-1) := by
  apply bruhatMonomial_eq_of_factorization F (n + 1) _ _ (simpleUpper F n i u) 1
  simp [simpleBruhatRepresentative, simpleUpper, mul_assoc]

/-- An actual canonical Bruhat cell representative and its double simple-Weyl update. -/
def oppositeCrossingMatrix (n : ℕ) (i k : Fin n) (m : MonomialGroup F (n + 1))
    (u v : F) : Matrix.GeneralLinearGroup (Fin (n + 1)) F :=
  monomialToGL F (n + 1) (rootWMonomial F i.castSucc i.succ 1) *
    Matrix.GeneralLinearGroup.elementary i.castSucc i.succ i.castSucc_lt_succ.ne u *
    monomialToGL F (n + 1) m *
    Matrix.GeneralLinearGroup.elementary k.castSucc k.succ k.castSucc_lt_succ.ne v *
    monomialToGL F (n + 1) (rootWMonomial F k.castSucc k.succ (-1))

lemma oppositeCrossingMatrix_eq (n : ℕ) (i k : Fin n)
    (m : MonomialGroup F (n + 1)) (u v : F) :
    oppositeCrossingMatrix F n i k m u v =
      monomialToGL F (n + 1) (rootWMonomial F i.castSucc i.succ 1) *
        simpleBruhatRepresentative F n i k m u v *
        monomialToGL F (n + 1) (rootWMonomial F k.castSucc k.succ (-1)) := by
  simp only [oppositeCrossingMatrix, simpleBruhatRepresentative, mul_assoc]

/-- The opposite-root pivot formula, uniform in both input parameters. -/
theorem opposite_crossing_bruhat_nonzero (n : ℕ) (i k : Fin n)
    (m : MonomialGroup F (n + 1))
    (hk : m.right k.castSucc = i.succ) (hl : m.right k.succ = i.castSucc)
    (u v : F) (d : Fˣ)
    (hd : (d : F) = u * v - (oppositeRootCoefficient F m i.castSucc i.succ : F)) :
    bruhatMonomial F (n + 1) (oppositeCrossingMatrix F n i k m u v) =
      rootHMonomial F i.castSucc i.succ (-d⁻¹) * m := by
  apply bruhatMonomial_eq_of_factorization F (n + 1) _ _
    (simpleUpper F n i (-v / (d : F))) (simpleUpper F n k (-u / (d : F)))
  exact opposite_crossing_factorization_nonzero F m i.castSucc i.succ
    k.castSucc k.succ i.castSucc_lt_succ.ne k.castSucc_lt_succ.ne hk hl u v
    (oppositeRootCoefficient F m i.castSucc i.succ) d
    (oppositeRootCoefficient_spec F m i.castSucc i.succ) hd

/-- The zero denominator uses a Weyl factor, with no inverse of that denominator. -/
theorem opposite_crossing_bruhat_zero (n : ℕ) (i k : Fin n)
    (m : MonomialGroup F (n + 1))
    (hk : m.right k.castSucc = i.succ) (hl : m.right k.succ = i.castSucc)
    (u v : Fˣ)
    (hzero : (u : F) * (v : F) = (oppositeRootCoefficient F m i.castSucc i.succ : F)) :
    bruhatMonomial F (n + 1) (oppositeCrossingMatrix F n i k m (u : F) (v : F)) =
      rootWMonomial F i.castSucc i.succ v * m := by
  apply bruhatMonomial_eq_of_factorization F (n + 1) _ _
    (simpleUpper F n i (-((u⁻¹ : Fˣ) : F))) 1
  simpa only [oppositeCrossingMatrix, simpleUpper, Subgroup.coe_one, mul_one] using
    opposite_crossing_factorization_zero F m i.castSucc i.succ k.castSucc k.succ
      i.castSucc_lt_succ.ne k.castSucc_lt_succ.ne hk hl u v
      (oppositeRootCoefficient F m i.castSucc i.succ)
      (oppositeRootCoefficient_spec F m i.castSucc i.succ) hzero

/-- Exhaustive scalar form of the opposite-root pivot branches, over every field. -/
theorem opposite_crossing_bruhat_cases (n : ℕ) (i k : Fin n)
    (m : MonomialGroup F (n + 1))
    (hk : m.right k.castSucc = i.succ) (hl : m.right k.succ = i.castSucc)
    (u v : F) :
    (∃ d : Fˣ,
      (d : F) = u * v - (oppositeRootCoefficient F m i.castSucc i.succ : F) ∧
      bruhatMonomial F (n + 1) (oppositeCrossingMatrix F n i k m u v) =
        rootHMonomial F i.castSucc i.succ (-d⁻¹) * m) ∨
    (∃ u' v' : Fˣ, (u' : F) = u ∧ (v' : F) = v ∧
      u * v = (oppositeRootCoefficient F m i.castSucc i.succ : F) ∧
      bruhatMonomial F (n + 1) (oppositeCrossingMatrix F n i k m u v) =
        rootWMonomial F i.castSucc i.succ v' * m) := by
  by_cases hd : u * v - (oppositeRootCoefficient F m i.castSucc i.succ : F) = 0
  · obtain ⟨hu, hv⟩ := opposite_crossing_zero_parameters F u v
      (oppositeRootCoefficient F m i.castSucc i.succ) hd
    right
    refine ⟨Units.mk0 u hu, Units.mk0 v hv, rfl, rfl, sub_eq_zero.mp hd, ?_⟩
    exact opposite_crossing_bruhat_zero F n i k m hk hl
      (Units.mk0 u hu) (Units.mk0 v hv) (sub_eq_zero.mp hd)
  · left
    refine ⟨Units.mk0 _ hd, rfl, ?_⟩
    exact opposite_crossing_bruhat_nonzero F n i k m hk hl u v (Units.mk0 _ hd) rfl

end Matrix.Bruhat

end

end

/-! ## EqualPivot -/

section

noncomputable section
universe u
namespace Matrix.Bruhat
variable (F : Type u) [Field F]

/-- Equal transported roots retain the actual positive ratio of the two matrix rows. -/
lemma equal_elementary_transport {n : ℕ}
    (m : MonomialGroup F n) (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (hk : m.right k = i) (hl : m.right l = j)
    (v : F) (c : Fˣ) (hc : m.left i = c * m.left j) :
    monomialToGL F n m * Matrix.GeneralLinearGroup.elementary k l hkl v =
      Matrix.GeneralLinearGroup.elementary i j hij ((c : F) * v) * monomialToGL F n m := by
  have hc' : (m.left i : F) = (c : F) * (m.left j : F) := by
    simpa only [Units.val_mul] using congrArg (fun z : Fˣ => (z : F)) hc
  have hcoef : (m.left i : F) * v * ((m.left j)⁻¹ : Fˣ) = (c : F) * v := by
    rw [hc']
    simp only [Units.val_inv_eq_inv_val]
    field_simp
  have he := monomial_conjugate_elementary F m k l hkl v
  have he' : monomialToGL F n m * Matrix.GeneralLinearGroup.elementary k l hkl v *
      (monomialToGL F n m)⁻¹ = Matrix.GeneralLinearGroup.elementary i j hij ((c : F) * v) := by
    simpa only [hk, hl, hcoef] using he
  have hh := congrArg (fun z : Matrix.GeneralLinearGroup (Fin n) F => z * monomialToGL F n m)
    he'
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh

/-- The two actual simple upper factors combine into the left entry `u+c*v`. -/
lemma equal_combine_left {n : ℕ}
    (m : MonomialGroup F n) (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (hk : m.right k = i) (hl : m.right l = j)
    (u v : F) (c : Fˣ) (hc : m.left i = c * m.left j) :
    Matrix.GeneralLinearGroup.elementary i j hij u * monomialToGL F n m *
        Matrix.GeneralLinearGroup.elementary k l hkl v =
      Matrix.GeneralLinearGroup.elementary i j hij (u + (c : F) * v) * monomialToGL F n m := by
  rw [mul_assoc, equal_elementary_transport F m i j k l hij hkl hk hl v c hc,
    ← mul_assoc, Matrix.GeneralLinearGroup.elementary_mul_same]

/-- The same combined entry on the right is `v+u/c`, including all cancellations. -/
lemma equal_combine_right {n : ℕ}
    (m : MonomialGroup F n) (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (hk : m.right k = i) (hl : m.right l = j)
    (u v : F) (c : Fˣ) (hc : m.left i = c * m.left j) :
    Matrix.GeneralLinearGroup.elementary i j hij u * monomialToGL F n m *
        Matrix.GeneralLinearGroup.elementary k l hkl v =
      monomialToGL F n m * Matrix.GeneralLinearGroup.elementary k l hkl (v + u / (c : F)) := by
  have hparam : (c : F) * (v + u / (c : F)) = u + (c : F) * v := by
    field_simp
    ring
  rw [equal_combine_left F m i j k l hij hkl hk hl u v c hc,
    equal_elementary_transport F m i j k l hij hkl hk hl (v + u / (c : F)) c hc,
    hparam]

/-- A nonzero combined entry creates the exact signed Weyl factor `W(c/t)`. -/
lemma equal_crossing_factorization_nonzero {n : ℕ}
    (m : MonomialGroup F n) (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (hk : m.right k = i) (hl : m.right l = j)
    (u v : F) (c t : Fˣ) (hc : m.left i = c * m.left j)
    (ht : (t : F) = u + (c : F) * v) :
    monomialToGL F n (rootWMonomial F i j 1) *
        Matrix.GeneralLinearGroup.elementary i j hij u * monomialToGL F n m *
        Matrix.GeneralLinearGroup.elementary k l hkl v *
        monomialToGL F n (rootWMonomial F k l (-1)) =
      Matrix.GeneralLinearGroup.elementary i j hij (-((t⁻¹ : Fˣ) : F)) *
        monomialToGL F n (rootWMonomial F i j (c * t⁻¹) * m) *
        Matrix.GeneralLinearGroup.elementary k l hkl (-(c : F) / (t : F)) := by
  have hc' : (m.left i : F) = (c : F) * (m.left j : F) := by
    simpa only [Units.val_mul] using congrArg (fun z : Fˣ => (z : F)) hc
  have hpi (s : Fin n) : i = m.right s ↔ s = k := by
    rw [← hk, m.right.injective.eq_iff, eq_comm]
  have hpj (s : Fin n) : j = m.right s ↔ s = l := by
    rw [← hl, m.right.injective.eq_iff, eq_comm]
  rw [mul_assoc (monomialToGL F n (rootWMonomial F i j 1))
    (Matrix.GeneralLinearGroup.elementary i j hij u) (monomialToGL F n m)]
  apply Units.ext
  ext r s
  rw [map_mul]
  simp only [mul_rootW_val F k l hkl, rootW_mul_val F i j hij,
    elementary_mul_val, mul_elementary_val, matrixMonomial_val]
  by_cases hri : r = i <;> by_cases hrj : r = j <;>
    by_cases hsk : s = k <;> by_cases hsl : s = l <;>
      simp [hri, hrj, hsk, hsl, hij, hij.symm, hkl, hkl.symm,
        hpi, hpj, hk, hl, hc', Units.val_inv_eq_inv_val]
  all_goals field_simp
  all_goals rw [ht]
  all_goals ring

/-- A vanishing combined entry is a literal diagonal monomial, without inverting it. -/
lemma equal_crossing_factorization_zero {n : ℕ}
    (m : MonomialGroup F n) (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (hk : m.right k = i) (hl : m.right l = j)
    (u v : F) (c : Fˣ) (hc : m.left i = c * m.left j)
    (ht : u + (c : F) * v = 0) :
    monomialToGL F n (rootWMonomial F i j 1) *
        Matrix.GeneralLinearGroup.elementary i j hij u * monomialToGL F n m *
        Matrix.GeneralLinearGroup.elementary k l hkl v *
        monomialToGL F n (rootWMonomial F k l (-1)) =
      monomialToGL F n (rootHMonomial F i j c⁻¹ * m) := by
  have hc' : (m.left i : F) = (c : F) * (m.left j : F) := by
    simpa only [Units.val_mul] using congrArg (fun z : Fˣ => (z : F)) hc
  have hu : u = -(c : F) * v := by
    simpa only [neg_mul] using eq_neg_of_add_eq_zero_left ht
  have hpi (s : Fin n) : i = m.right s ↔ s = k := by
    rw [← hk, m.right.injective.eq_iff, eq_comm]
  have hpj (s : Fin n) : j = m.right s ↔ s = l := by
    rw [← hl, m.right.injective.eq_iff, eq_comm]
  rw [mul_assoc (monomialToGL F n (rootWMonomial F i j 1))
    (Matrix.GeneralLinearGroup.elementary i j hij u) (monomialToGL F n m)]
  apply Units.ext
  ext r s
  rw [map_mul]
  simp only [mul_rootW_val F k l hkl, rootW_mul_val F i j hij,
    elementary_mul_val, mul_elementary_val, rootH_mul_val F i j hij, matrixMonomial_val]
  by_cases hri : r = i <;> by_cases hrj : r = j <;>
    by_cases hsk : s = k <;> by_cases hsl : s = l <;>
      simp [hri, hrj, hsk, hsl, hij, hij.symm, hkl, hkl.symm,
        hpi, hpj, hk, hl, hc', hu, Units.val_inv_eq_inv_val]
  all_goals field_simp
  all_goals ring

/-- Both left and right combined pivots vanish together, since the ratio is a unit. -/
lemma equal_combined_pivots_zero_iff (u v : F) (c : Fˣ) :
    u + (c : F) * v = 0 ↔ v + u / (c : F) = 0 := by
  have hparam : (c : F) * (v + u / (c : F)) = u + (c : F) * v := by
    field_simp
    ring
  rw [← hparam, mul_eq_zero]
  simp only [c.ne_zero, false_or]

end Matrix.Bruhat

end

end

/-! ## EqualBruhat -/

section

noncomputable section
universe u
namespace Matrix.Bruhat
variable (F : Type u) [Field F]

/-- The equal-root coefficient is the actual positive ratio of the two monomial rows. -/
def equalRootCoefficient {n : ℕ} (m : MonomialGroup F n) (i j : Fin n) : Fˣ :=
  m.left i * (m.left j)⁻¹

lemma equalRootCoefficient_spec {n : ℕ} (m : MonomialGroup F n) (i j : Fin n) :
    m.left i = equalRootCoefficient F m i j * m.left j := by
  simp [equalRootCoefficient, mul_assoc]

/-- The actual combined left entry on an equal-root cell representative. -/
theorem equal_representative_combine_left (n : ℕ) (i k : Fin n)
    (m : MonomialGroup F (n + 1))
    (hk : m.right k.castSucc = i.castSucc) (hl : m.right k.succ = i.succ)
    (u v : F) :
    simpleBruhatRepresentative F n i k m u v =
      Matrix.GeneralLinearGroup.elementary i.castSucc i.succ i.castSucc_lt_succ.ne
        (u + (equalRootCoefficient F m i.castSucc i.succ : F) * v) *
        monomialToGL F (n + 1) m := by
  exact equal_combine_left F m i.castSucc i.succ k.castSucc k.succ
    i.castSucc_lt_succ.ne k.castSucc_lt_succ.ne hk hl u v
    (equalRootCoefficient F m i.castSucc i.succ)
    (equalRootCoefficient_spec F m i.castSucc i.succ)

/-- The same representative has right entry `v+u/c`, with the same exact row ratio. -/
theorem equal_representative_combine_right (n : ℕ) (i k : Fin n)
    (m : MonomialGroup F (n + 1))
    (hk : m.right k.castSucc = i.castSucc) (hl : m.right k.succ = i.succ)
    (u v : F) :
    simpleBruhatRepresentative F n i k m u v = monomialToGL F (n + 1) m *
      Matrix.GeneralLinearGroup.elementary k.castSucc k.succ k.castSucc_lt_succ.ne
        (v + u / (equalRootCoefficient F m i.castSucc i.succ : F)) := by
  exact equal_combine_right F m i.castSucc i.succ k.castSucc k.succ
    i.castSucc_lt_succ.ne k.castSucc_lt_succ.ne hk hl u v
    (equalRootCoefficient F m i.castSucc i.succ)
    (equalRootCoefficient_spec F m i.castSucc i.succ)

/-- The left intermediate projection is a Weyl branch for every input parameter. -/
theorem equal_left_bruhat (n : ℕ) (i k : Fin n)
    (m : MonomialGroup F (n + 1))
    (hk : m.right k.castSucc = i.castSucc) (hl : m.right k.succ = i.succ)
    (u v : F) :
    bruhatMonomial F (n + 1)
      (monomialToGL F (n + 1) (rootWMonomial F i.castSucc i.succ 1) *
        simpleBruhatRepresentative F n i k m u v) =
      rootWMonomial F i.castSucc i.succ 1 * m := by
  apply bruhatMonomial_eq_of_factorization F (n + 1) _ _ 1
    (simpleUpper F n k (v + u / (equalRootCoefficient F m i.castSucc i.succ : F)))
  simp only [Subgroup.coe_one, one_mul, map_mul]
  change monomialToGL F (n + 1) (rootWMonomial F i.castSucc i.succ 1) *
      simpleBruhatRepresentative F n i k m u v =
    (monomialToGL F (n + 1) (rootWMonomial F i.castSucc i.succ 1) *
      monomialToGL F (n + 1) m) *
      Matrix.GeneralLinearGroup.elementary k.castSucc k.succ k.castSucc_lt_succ.ne
        (v + u / (equalRootCoefficient F m i.castSucc i.succ : F))
  rw [equal_representative_combine_right F n i k m hk hl u v, mul_assoc]

/-- The right intermediate projection is also a Weyl branch for every input parameter. -/
theorem equal_right_bruhat (n : ℕ) (i k : Fin n)
    (m : MonomialGroup F (n + 1))
    (hk : m.right k.castSucc = i.castSucc) (hl : m.right k.succ = i.succ)
    (u v : F) :
    bruhatMonomial F (n + 1)
      (simpleBruhatRepresentative F n i k m u v *
        monomialToGL F (n + 1) (rootWMonomial F k.castSucc k.succ (-1))) =
      m * rootWMonomial F k.castSucc k.succ (-1) := by
  apply bruhatMonomial_eq_of_factorization F (n + 1) _ _
    (simpleUpper F n i (u + (equalRootCoefficient F m i.castSucc i.succ : F) * v)) 1
  simp only [Subgroup.coe_one, mul_one, map_mul]
  change simpleBruhatRepresentative F n i k m u v *
      monomialToGL F (n + 1) (rootWMonomial F k.castSucc k.succ (-1)) =
    Matrix.GeneralLinearGroup.elementary i.castSucc i.succ i.castSucc_lt_succ.ne
      (u + (equalRootCoefficient F m i.castSucc i.succ : F) * v) *
      (monomialToGL F (n + 1) m *
        monomialToGL F (n + 1) (rootWMonomial F k.castSucc k.succ (-1)))
  rw [equal_representative_combine_left F n i k m hk hl u v, mul_assoc]

/-- The actual double update, with left `W(1)` and right `W(-1)` retained. -/
def equalCrossingMatrix (n : ℕ) (i k : Fin n) (m : MonomialGroup F (n + 1))
    (u v : F) : Matrix.GeneralLinearGroup (Fin (n + 1)) F :=
  monomialToGL F (n + 1) (rootWMonomial F i.castSucc i.succ 1) *
    simpleBruhatRepresentative F n i k m u v *
    monomialToGL F (n + 1) (rootWMonomial F k.castSucc k.succ (-1))

/-- A nonzero combined pivot has the exact monomial factor `W(c/t)*m`. -/
theorem equal_crossing_bruhat_nonzero (n : ℕ) (i k : Fin n)
    (m : MonomialGroup F (n + 1))
    (hk : m.right k.castSucc = i.castSucc) (hl : m.right k.succ = i.succ)
    (u v : F) (t : Fˣ)
    (ht : (t : F) = u + (equalRootCoefficient F m i.castSucc i.succ : F) * v) :
    bruhatMonomial F (n + 1) (equalCrossingMatrix F n i k m u v) =
      rootWMonomial F i.castSucc i.succ
        (equalRootCoefficient F m i.castSucc i.succ * t⁻¹) * m := by
  apply bruhatMonomial_eq_of_factorization F (n + 1) _ _
    (simpleUpper F n i (-((t⁻¹ : Fˣ) : F)))
    (simpleUpper F n k (-(equalRootCoefficient F m i.castSucc i.succ : F) / (t : F)))
  simpa only [equalCrossingMatrix, simpleBruhatRepresentative, simpleUpper, mul_assoc] using
    equal_crossing_factorization_nonzero F m i.castSucc i.succ k.castSucc k.succ
      i.castSucc_lt_succ.ne k.castSucc_lt_succ.ne hk hl u v
      (equalRootCoefficient F m i.castSucc i.succ) t
      (equalRootCoefficient_spec F m i.castSucc i.succ) ht

/-- A zero combined pivot gives a literal monomial, including nonzero cancellation. -/
theorem equal_crossing_bruhat_zero (n : ℕ) (i k : Fin n)
    (m : MonomialGroup F (n + 1))
    (hk : m.right k.castSucc = i.castSucc) (hl : m.right k.succ = i.succ)
    (u v : F)
    (ht : u + (equalRootCoefficient F m i.castSucc i.succ : F) * v = 0) :
    bruhatMonomial F (n + 1) (equalCrossingMatrix F n i k m u v) =
      rootHMonomial F i.castSucc i.succ (equalRootCoefficient F m i.castSucc i.succ)⁻¹ * m := by
  apply bruhatMonomial_eq_of_factorization F (n + 1) _ _ 1 1
  simpa only [equalCrossingMatrix, simpleBruhatRepresentative, Subgroup.coe_one,
    one_mul, mul_one, mul_assoc] using
    equal_crossing_factorization_zero F m i.castSucc i.succ k.castSucc k.succ
      i.castSucc_lt_succ.ne k.castSucc_lt_succ.ne hk hl u v
      (equalRootCoefficient F m i.castSucc i.succ)
      (equalRootCoefficient_spec F m i.castSucc i.succ) ht

/-- Exhaustive equal-root branches for arbitrary scalar input parameters. -/
theorem equal_crossing_bruhat_cases (n : ℕ) (i k : Fin n)
    (m : MonomialGroup F (n + 1))
    (hk : m.right k.castSucc = i.castSucc) (hl : m.right k.succ = i.succ)
    (u v : F) :
    (u + (equalRootCoefficient F m i.castSucc i.succ : F) * v = 0 ∧
      bruhatMonomial F (n + 1) (equalCrossingMatrix F n i k m u v) =
        rootHMonomial F i.castSucc i.succ (equalRootCoefficient F m i.castSucc i.succ)⁻¹ * m) ∨
    (∃ t : Fˣ,
      (t : F) = u + (equalRootCoefficient F m i.castSucc i.succ : F) * v ∧
      bruhatMonomial F (n + 1) (equalCrossingMatrix F n i k m u v) =
        rootWMonomial F i.castSucc i.succ
          (equalRootCoefficient F m i.castSucc i.succ * t⁻¹) * m) := by
  by_cases ht : u + (equalRootCoefficient F m i.castSucc i.succ : F) * v = 0
  · exact Or.inl ⟨ht, equal_crossing_bruhat_zero F n i k m hk hl u v ht⟩
  · exact Or.inr ⟨Units.mk0 _ ht, rfl,
      equal_crossing_bruhat_nonzero F n i k m hk hl u v (Units.mk0 _ ht) rfl⟩

/-- All scalar reasons for a vanishing combined pivot, without an inverse of that pivot. -/
theorem equal_combined_pivot_zero_cases (u v : F) (c : Fˣ) :
    u + (c : F) * v = 0 ↔
      (u = 0 ∧ v = 0) ∨ (u ≠ 0 ∧ v ≠ 0 ∧ u = -(c : F) * v) := by
  by_cases hu : u = 0
  · subst u
    simp [c.ne_zero]
  · by_cases hv : v = 0
    · subst v
      simp [hu]
    · constructor
      · intro ht
        exact Or.inr ⟨hu, hv, by
          simpa only [neg_mul] using eq_neg_of_add_eq_zero_left ht⟩
      · rintro (⟨hu0, _⟩ | ⟨_, _, ht⟩)
        · exact (hu hu0).elim
        · rw [ht]
          ring

end Matrix.Bruhat

end

end
