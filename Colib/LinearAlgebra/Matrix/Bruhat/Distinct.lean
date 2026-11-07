/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, kangxyz
-/
module

public import Colib.LinearAlgebra.Matrix.Bruhat.RootUpdate
public import Colib.LinearAlgebra.Matrix.Bruhat.Opposite
public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary
public import Colib.LinearAlgebra.Matrix.Bruhat.Coordinates
public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.Stabilization
public import Colib.LinearAlgebra.Matrix.Bruhat.Decomposition

/-!
# Distinct

Finite matrix Bruhat distinct over fields, using the native general linear
group, with the original rank hypotheses and signed matrix formulas.

## Implementation provenance

Adapted from `Quillen/Aglib/LinearAlgebra/Matrix/Bruhat/Distinct.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Native elementary matrix units and
finite matrix stabilization are used directly.
-/

@[expose] public section

/-! ## DistinctOrder -/

section

namespace Matrix.Bruhat

/-- An adjacent swap changes the order of a distinct pair only for its own two entries. -/
lemma adjacent_swap_lt_iff_of_distinct_pair {n : ℕ} (k : Fin n)
    (p q : Fin (n + 1))
    (hpos : ¬(p = k.castSucc ∧ q = k.succ))
    (hneg : ¬(p = k.succ ∧ q = k.castSucc)) :
    Equiv.swap k.castSucc k.succ p < Equiv.swap k.castSucc k.succ q ↔ p < q := by
  by_cases hp0 : p = k.castSucc <;> by_cases hp1 : p = k.succ <;>
    by_cases hq0 : q = k.castSucc <;> by_cases hq1 : q = k.succ <;>
      simp_all [Equiv.swap_apply_def]
  all_goals simp only [Fin.lt_def, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ] at *
  all_goals omega

/-- For distinct transported roots, the right simple swap preserves the left pivot order. -/
lemma distinct_right_swap_preserves_left_order {n : ℕ} (i k : Fin n)
    (σ : Equiv.Perm (Fin (n + 1)))
    (hpos : ¬(σ k.castSucc = i.castSucc ∧ σ k.succ = i.succ))
    (hneg : ¬(σ k.castSucc = i.succ ∧ σ k.succ = i.castSucc)) :
    (σ * Equiv.swap k.castSucc k.succ).symm i.castSucc <
        (σ * Equiv.swap k.castSucc k.succ).symm i.succ ↔
      σ.symm i.castSucc < σ.symm i.succ := by
  apply adjacent_swap_lt_iff_of_distinct_pair k (σ.symm i.castSucc) (σ.symm i.succ)
  · rintro ⟨hi, hj⟩
    apply hpos
    constructor
    · exact (congrArg σ hi).symm.trans (σ.apply_symm_apply _)
    · exact (congrArg σ hj).symm.trans (σ.apply_symm_apply _)
  · rintro ⟨hi, hj⟩
    apply hneg
    constructor
    · exact (congrArg σ hj).symm.trans (σ.apply_symm_apply _)
    · exact (congrArg σ hi).symm.trans (σ.apply_symm_apply _)

end Matrix.Bruhat

end

/-! ## DistinctPivot -/

section

noncomputable section
universe u
namespace Matrix.Bruhat
variable (F : Type u) [Field F]

/-- A literal elementary matrix has zero entry at a different simple root. -/
lemma elementary_other_simple_entry (n : ℕ) (i : Fin n)
    (r s : Fin (n + 1)) (hrs : r ≠ s)
    (hother : ¬(r = i.castSucc ∧ s = i.succ)) (a : F) :
    (Matrix.GeneralLinearGroup.elementary r s hrs a).val i.castSucc i.succ = 0 := by
  have hij : i.castSucc ≠ i.succ := i.castSucc_lt_succ.ne
  simp [Matrix.GeneralLinearGroup.elementary_val,
    Matrix.single, hij, hother]

/-- Move an actual elementary matrix through an actual monomial, retaining its coefficient. -/
lemma monomial_mul_elementary_eq {n : ℕ} (m : MonomialGroup F n)
    (k l : Fin n) (hkl : k ≠ l) (a : F) :
    monomialToGL F n m * Matrix.GeneralLinearGroup.elementary k l hkl a =
      Matrix.GeneralLinearGroup.elementary (m.right k) (m.right l) (m.right.injective.ne hkl)
        ((m.left (m.right k) : F) * a * ((m.left (m.right l))⁻¹ : Fˣ)) *
          monomialToGL F n m := by
  have h := congrArg (fun z : Matrix.GeneralLinearGroup (Fin n) F => z * monomialToGL F n m)
    (monomial_conjugate_elementary F m k l hkl a)
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using h

/-- The original finite right Gauss factorization, with the retained W(-1) sign. -/
lemma simple_right_gauss {n : ℕ} (k l : Fin n) (hkl : k ≠ l) (a : Fˣ) :
    Matrix.GeneralLinearGroup.elementary k l hkl (a : F) *
        monomialToGL F n (rootWMonomial F k l (-1)) =
      Matrix.GeneralLinearGroup.elementary l k hkl.symm ((a⁻¹ : Fˣ) : F) *
        monomialToGL F n (rootHMonomial F k l a) *
        Matrix.GeneralLinearGroup.elementary k l hkl (-((a⁻¹ : Fˣ) : F)) := by
  simpa only [Matrix.GeneralLinearGroup.elementary_zero, map_one, one_mul, zero_sub, Units.val_neg,
    Units.val_one, neg_div, neg_neg, Units.val_inv_eq_inv_val, one_div] using
    opposite_right_factorization_nonzero F (1 : MonomialGroup F n) l k k l
      hkl.symm hkl rfl rfl 0 a (-1) (by simp)

/-- Splitting an actual upper factor leaves a conjugatable remainder with zero simple entry. -/
lemma simple_left_remainder (n : ℕ) (i : Fin n) (U : upperUnipotent F (n + 1)) :
    ∃ U₁ : upperUnipotent F (n + 1),
      monomialToGL F (n + 1) (rootWMonomial F i.castSucc i.succ 1) * U =
        (U₁ : Matrix.GeneralLinearGroup (Fin (n + 1)) F) *
          monomialToGL F (n + 1) (rootWMonomial F i.castSucc i.succ 1) *
          Matrix.GeneralLinearGroup.elementary i.castSucc i.succ i.castSucc_lt_succ.ne
            ((U : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val i.castSucc i.succ) := by
  let w := rootWMonomial F i.castSucc i.succ (1 : Fˣ)
  let W := monomialToGL F (n + 1) w
  obtain ⟨U₀, hz, hU⟩ := split_simple_upper F n i U
  let U₁ : upperUnipotent F (n + 1) :=
    ⟨W * U₀ * W⁻¹, upper_simple_reflection_conjugate F n i w.left U₀ hz⟩
  refine ⟨U₁, ?_⟩
  change W * U = (W * U₀ * W⁻¹) * W * _
  nth_rw 1 [hU]
  simp [simpleUpper, mul_assoc]

/-- An increasing transported left root, or a zero pivot, gives the exact Weyl branch. -/
theorem left_simple_pivot_weyl (n : ℕ) (i : Fin n) (m : MonomialGroup F (n + 1))
    (U V : upperUnipotent F (n + 1))
    (hbranch : (U : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val i.castSucc i.succ = 0 ∨
      m.right.symm i.castSucc < m.right.symm i.succ) :
    bruhatMonomial F (n + 1)
      (monomialToGL F (n + 1) (rootWMonomial F i.castSucc i.succ 1) *
        ((U : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * monomialToGL F (n + 1) m * V)) =
      rootWMonomial F i.castSucc i.succ 1 * m := by
  let W := monomialToGL F (n + 1) (rootWMonomial F i.castSucc i.succ 1)
  let M := monomialToGL F (n + 1) m
  let t := (U : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val i.castSucc i.succ
  obtain ⟨U₁, hU⟩ := simple_left_remainder F n i U
  change W * (U : Matrix.GeneralLinearGroup (Fin (n + 1)) F) = U₁ * W *
    Matrix.GeneralLinearGroup.elementary i.castSucc i.succ i.castSucc_lt_succ.ne t at hU
  have hmove : ∃ R : upperUnipotent F (n + 1),
      Matrix.GeneralLinearGroup.elementary i.castSucc i.succ i.castSucc_lt_succ.ne t * M = M * R :=
        by
    rcases hbranch with ht | hord
    · refine ⟨1, ?_⟩
      change Matrix.GeneralLinearGroup.elementary i.castSucc i.succ i.castSucc_lt_succ.ne t * M = M
        * 1
      simp only [t, ht, Matrix.GeneralLinearGroup.elementary_zero, one_mul, mul_one]
    · exact elementary_mul_monomial_upper F m i.castSucc i.succ
        i.castSucc_lt_succ.ne t hord
  obtain ⟨R, hR⟩ := hmove
  apply bruhatMonomial_eq_of_factorization F (n + 1) _ _ U₁ (R * V)
  rw [map_mul]
  change W * ((U : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * M * V) = U₁ * (W * M) * (R *
    V)
  calc
    _ = (W * U) * (M * V) := by simp [mul_assoc]
    _ = (U₁ : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * W *
        (Matrix.GeneralLinearGroup.elementary i.castSucc i.succ i.castSucc_lt_succ.ne t * M) * V :=
          by
      rw [hU]
      simp [t, mul_assoc]
    _ = _ := by rw [hR]; simp [mul_assoc]

/-- A nonzero decreasing pivot gives the exact diagonal branch, for actual upper factors. -/
theorem left_simple_pivot_diagonal (n : ℕ) (i : Fin n) (m : MonomialGroup F (n + 1))
    (U V : upperUnipotent F (n + 1)) (t : Fˣ)
    (ht : (U : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val i.castSucc i.succ = (t : F))
    (hdesc : m.right.symm i.succ < m.right.symm i.castSucc) :
    bruhatMonomial F (n + 1)
      (monomialToGL F (n + 1) (rootWMonomial F i.castSucc i.succ 1) *
        ((U : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * monomialToGL F (n + 1) m * V)) =
      (rootHMonomial F i.castSucc i.succ (-t))⁻¹ * m := by
  let W := monomialToGL F (n + 1) (rootWMonomial F i.castSucc i.succ 1)
  let M := monomialToGL F (n + 1) m
  let a : Fˣ := -t
  obtain ⟨U₁, hU⟩ := simple_left_remainder F n i U
  change W * (U : Matrix.GeneralLinearGroup (Fin (n + 1)) F) = U₁ * W *
    Matrix.GeneralLinearGroup.elementary i.castSucc i.succ i.castSucc_lt_succ.ne
      ((U : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val i.castSucc i.succ) at hU
  have hgauss := rootWMonomial_gauss F i.castSucc i.succ i.castSucc_lt_succ.ne a
  have hentry : -(a : F) = (t : F) := by simp [a]
  rw [hentry] at hgauss
  obtain ⟨R, hR⟩ := elementary_mul_monomial_upper F m i.succ i.castSucc
    i.castSucc_lt_succ.ne.symm (-((a⁻¹ : Fˣ) : F)) hdesc
  let U₂ := U₁ * simpleUpper F n i ((a⁻¹ : Fˣ) : F)
  apply bruhatMonomial_eq_of_factorization F (n + 1) _ _ U₂ (R * V)
  rw [map_mul, map_inv]
  change W * ((U : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * M * V) =
    (U₁ * Matrix.GeneralLinearGroup.elementary i.castSucc i.succ i.castSucc_lt_succ.ne
      ((a⁻¹ : Fˣ) : F)) *
      ((monomialToGL F (n + 1) (rootHMonomial F i.castSucc i.succ a))⁻¹ * M) * (R * V)
  have hleft : W * (U : Matrix.GeneralLinearGroup (Fin (n + 1)) F) =
      (U₁ : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * W *
        Matrix.GeneralLinearGroup.elementary i.castSucc i.succ i.castSucc_lt_succ.ne (t : F) := by
    simpa only [ht] using hU
  calc
    _ = (W * U) * (M * V) := by simp [mul_assoc]
    _ = (U₁ : Matrix.GeneralLinearGroup (Fin (n + 1)) F) *
        (W * Matrix.GeneralLinearGroup.elementary i.castSucc i.succ i.castSucc_lt_succ.ne (t : F)) *
        (M * V) := by rw [hleft]; simp [mul_assoc]
    _ = _ := by
      rw [hgauss]
      change U₁ * (_ * _ * Matrix.GeneralLinearGroup.elementary i.succ i.castSucc
        i.castSucc_lt_succ.ne.symm (-((a⁻¹ : Fˣ) : F))) * (M * V) = _
      have he : Matrix.GeneralLinearGroup.elementary i.succ i.castSucc i.castSucc_lt_succ.ne.symm
          (-((a⁻¹ : Fˣ) : F)) * (M * V) = M * (R * V) := by
        rw [← mul_assoc, hR, mul_assoc]
      simp only [mul_assoc]
      rw [he]

end Matrix.Bruhat

end

end

/-! ## DistinctBruhat -/

section

noncomputable section
universe u
namespace Matrix.Bruhat
variable (F : Type u) [Field F]

/-- The actual right update preserves the other simple entry and its permutation order test. -/
theorem distinct_right_factorization (n : ℕ) (i k : Fin n)
    (m : MonomialGroup F (n + 1))
    (hpos : ¬(m.right k.castSucc = i.castSucc ∧ m.right k.succ = i.succ))
    (hneg : ¬(m.right k.castSucc = i.succ ∧ m.right k.succ = i.castSucc))
    (u v : F) :
    ∃ (N : MonomialGroup F (n + 1)) (U V : upperUnipotent F (n + 1)),
      simpleBruhatRepresentative F n i k m u v *
          monomialToGL F (n + 1) (rootWMonomial F k.castSucc k.succ (-1)) =
        (U : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * monomialToGL F (n + 1) N * V ∧
      (U : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val i.castSucc i.succ = u ∧
      (N.right.symm i.castSucc < N.right.symm i.succ ↔
        m.right.symm i.castSucc < m.right.symm i.succ) := by
  let M := monomialToGL F (n + 1) m
  let w := rootWMonomial F k.castSucc k.succ (-1)
  have hworder : ((m * w).right.symm i.castSucc < (m * w).right.symm i.succ ↔
      m.right.symm i.castSucc < m.right.symm i.succ) := by
    change (m.right * Equiv.swap k.castSucc k.succ).symm i.castSucc <
        (m.right * Equiv.swap k.castSucc k.succ).symm i.succ ↔ _
    exact distinct_right_swap_preserves_left_order i k m.right hpos hneg
  by_cases hv : v = 0
  · subst v
    refine ⟨m * w, simpleUpper F n i u, 1, ?_, simpleUpper_entry F n i u, hworder⟩
    simp [simpleBruhatRepresentative, simpleUpper, w, mul_assoc]
  by_cases hγ : m.right k.castSucc < m.right k.succ
  · let b : F := (m.left (m.right k.castSucc) : F) * v *
      ((m.left (m.right k.succ))⁻¹ : Fˣ)
    let R : upperUnipotent F (n + 1) :=
      ⟨Matrix.GeneralLinearGroup.elementary (m.right k.castSucc) (m.right k.succ)
        (m.right.injective.ne k.castSucc_lt_succ.ne) b,
        elementary_mem_upper F _ _ hγ b⟩
    let U := simpleUpper F n i u * R
    have hmove : M * Matrix.GeneralLinearGroup.elementary k.castSucc k.succ k.castSucc_lt_succ.ne v
      =
        (R : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * M :=
      monomial_mul_elementary_eq F m k.castSucc k.succ k.castSucc_lt_succ.ne v
    have hentry : (U : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val i.castSucc i.succ = u :=
      by
      dsimp only [U]
      rw [upper_adjacent_mul, simpleUpper_entry]
      change u + (Matrix.GeneralLinearGroup.elementary (m.right k.castSucc) (m.right k.succ)
        (m.right.injective.ne k.castSucc_lt_succ.ne) b).val i.castSucc i.succ = u
      rw [elementary_other_simple_entry F n i _ _ _ hpos b, add_zero]
    refine ⟨m * w, U, 1, ?_, hentry, hworder⟩
    have hh := congrArg (fun z : Matrix.GeneralLinearGroup (Fin (n + 1)) F =>
      (simpleUpper F n i u : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * z *
        monomialToGL F (n + 1) w) hmove
    simpa only [simpleBruhatRepresentative, U, simpleUpper, M, Subgroup.coe_mul,
      Subgroup.coe_one, mul_one, map_mul, mul_assoc] using hh
  · have hne := m.right.injective.ne k.castSucc_lt_succ.ne
    have hrev : m.right k.succ < m.right k.castSucc :=
      lt_of_le_of_ne (le_of_not_gt hγ) (Ne.symm hne)
    let a : Fˣ := Units.mk0 v hv
    let h := rootHMonomial F k.castSucc k.succ a
    let b : F := (m.left (m.right k.succ) : F) * ((a⁻¹ : Fˣ) : F) *
      ((m.left (m.right k.castSucc))⁻¹ : Fˣ)
    let R : upperUnipotent F (n + 1) :=
      ⟨Matrix.GeneralLinearGroup.elementary (m.right k.succ) (m.right k.castSucc)
        (m.right.injective.ne k.castSucc_lt_succ.ne.symm) b,
        elementary_mem_upper F _ _ hrev b⟩
    let U := simpleUpper F n i u * R
    have hother : ¬(m.right k.succ = i.castSucc ∧ m.right k.castSucc = i.succ) := by
      rintro ⟨h1, h0⟩
      exact hneg ⟨h0, h1⟩
    have hentry : (U : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val i.castSucc i.succ = u :=
      by
      dsimp only [U]
      rw [upper_adjacent_mul, simpleUpper_entry]
      change u + (Matrix.GeneralLinearGroup.elementary (m.right k.succ) (m.right k.castSucc)
        (m.right.injective.ne k.castSucc_lt_succ.ne.symm) b).val i.castSucc i.succ = u
      rw [elementary_other_simple_entry F n i _ _ _ hother b, add_zero]
    have hmove : M * Matrix.GeneralLinearGroup.elementary k.succ k.castSucc
      k.castSucc_lt_succ.ne.symm
          ((a⁻¹ : Fˣ) : F) = (R : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * M :=
      monomial_mul_elementary_eq F m k.succ k.castSucc k.castSucc_lt_succ.ne.symm
        ((a⁻¹ : Fˣ) : F)
    have hgauss : Matrix.GeneralLinearGroup.elementary k.castSucc k.succ k.castSucc_lt_succ.ne v *
        monomialToGL F (n + 1) w =
      Matrix.GeneralLinearGroup.elementary k.succ k.castSucc k.castSucc_lt_succ.ne.symm
        ((a⁻¹ : Fˣ) : F) * monomialToGL F (n + 1) h *
          Matrix.GeneralLinearGroup.elementary k.castSucc k.succ k.castSucc_lt_succ.ne
            (-((a⁻¹ : Fˣ) : F)) :=
      simple_right_gauss F k.castSucc k.succ k.castSucc_lt_succ.ne a
    have hbase : M *
        (Matrix.GeneralLinearGroup.elementary k.castSucc k.succ k.castSucc_lt_succ.ne v *
          monomialToGL F (n + 1) w) =
      (R : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * (M * monomialToGL F (n + 1) h) *
        Matrix.GeneralLinearGroup.elementary k.castSucc k.succ k.castSucc_lt_succ.ne
          (-((a⁻¹ : Fˣ) : F)) := by
      rw [hgauss]
      simpa only [mul_assoc] using congrArg (fun z : Matrix.GeneralLinearGroup (Fin (n + 1)) F
        =>
        z * monomialToGL F (n + 1) h *
          Matrix.GeneralLinearGroup.elementary k.castSucc k.succ k.castSucc_lt_succ.ne
            (-((a⁻¹ : Fˣ) : F))) hmove
    refine ⟨m * h, U, simpleUpper F n k (-((a⁻¹ : Fˣ) : F)), ?_, hentry, ?_⟩
    · have hh := congrArg (fun z : Matrix.GeneralLinearGroup (Fin (n + 1)) F =>
        (simpleUpper F n i u : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * z) hbase
      simpa only [simpleBruhatRepresentative, U, simpleUpper, M, Subgroup.coe_mul,
        map_mul, mul_assoc] using hh
    · change (m.right * 1).symm i.castSucc < (m.right * 1).symm i.succ ↔ _
      simp

/-- The actual monomial-ratio square for every distinct transported simple root. -/
theorem distinct_bruhat_ratio_square (n : ℕ) (i k : Fin n)
    (m : MonomialGroup F (n + 1))
    (hpos : ¬(m.right k.castSucc = i.castSucc ∧ m.right k.succ = i.succ))
    (hneg : ¬(m.right k.castSucc = i.succ ∧ m.right k.succ = i.castSucc))
    (u v : F) :
    bruhatMonomial F (n + 1)
      (monomialToGL F (n + 1) (rootWMonomial F i.castSucc i.succ 1) *
        simpleBruhatRepresentative F n i k m u v *
          monomialToGL F (n + 1) (rootWMonomial F k.castSucc k.succ (-1))) =
      bruhatMonomial F (n + 1)
          (monomialToGL F (n + 1) (rootWMonomial F i.castSucc i.succ 1) *
            simpleBruhatRepresentative F n i k m u v) *
        (bruhatMonomial F (n + 1) (simpleBruhatRepresentative F n i k m u v))⁻¹ *
      bruhatMonomial F (n + 1)
        (simpleBruhatRepresentative F n i k m u v *
          monomialToGL F (n + 1) (rootWMonomial F k.castSucc k.succ (-1))) := by
  obtain ⟨N, U, V, hright, hentry, horder⟩ :=
    distinct_right_factorization F n i k m hpos hneg u v
  have hR : bruhatMonomial F (n + 1)
      (simpleBruhatRepresentative F n i k m u v *
        monomialToGL F (n + 1) (rootWMonomial F k.castSucc k.succ (-1))) = N :=
    bruhatMonomial_eq_of_factorization F (n + 1) _ N U V hright
  have hP : monomialToGL F (n + 1) (rootWMonomial F i.castSucc i.succ 1) *
        simpleBruhatRepresentative F n i k m u v *
        monomialToGL F (n + 1) (rootWMonomial F k.castSucc k.succ (-1)) =
      monomialToGL F (n + 1) (rootWMonomial F i.castSucc i.succ 1) *
        ((U : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * monomialToGL F (n + 1) N * V) := by
    rw [mul_assoc, hright]
  rw [hP, simpleBruhatRepresentative_projection, hR]
  by_cases hu : u = 0
  · have hL := left_simple_pivot_weyl F n i m (simpleUpper F n i u)
      (simpleUpper F n k v) (Or.inl (by simpa only [simpleUpper_entry] using hu))
    have hP' := left_simple_pivot_weyl F n i N U V (Or.inl (hentry.trans hu))
    simp only [simpleBruhatRepresentative, simpleUpper] at hL ⊢
    rw [hP', hL]
    simp [mul_assoc]
  by_cases hord : m.right.symm i.castSucc < m.right.symm i.succ
  · have hL := left_simple_pivot_weyl F n i m (simpleUpper F n i u)
      (simpleUpper F n k v) (Or.inr hord)
    have hP' := left_simple_pivot_weyl F n i N U V (Or.inr (horder.mpr hord))
    simp only [simpleBruhatRepresentative, simpleUpper] at hL ⊢
    rw [hP', hL]
    simp [mul_assoc]
  · have hdesc : m.right.symm i.succ < m.right.symm i.castSucc :=
      lt_of_le_of_ne (le_of_not_gt hord)
        (Ne.symm (m.right.symm.injective.ne i.castSucc_lt_succ.ne))
    have hNnot : ¬(N.right.symm i.castSucc < N.right.symm i.succ) :=
      fun h => hord (horder.mp h)
    have hNdesc : N.right.symm i.succ < N.right.symm i.castSucc :=
      lt_of_le_of_ne (le_of_not_gt hNnot)
        (Ne.symm (N.right.symm.injective.ne i.castSucc_lt_succ.ne))
    let t : Fˣ := Units.mk0 u hu
    have hL := left_simple_pivot_diagonal F n i m (simpleUpper F n i u)
      (simpleUpper F n k v) t (simpleUpper_entry F n i u) hdesc
    have hP' := left_simple_pivot_diagonal F n i N U V t hentry hNdesc
    simp only [simpleBruhatRepresentative, simpleUpper] at hL ⊢
    rw [hP', hL]
    simp [mul_assoc]

end Matrix.Bruhat

end

end
