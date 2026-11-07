/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, kangxyz
-/
module

public import Colib.LinearAlgebra.Matrix.Bruhat.Coordinates
public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.Stabilization
public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary

/-!
# Decomposition

Finite matrix Bruhat decomposition over fields, using the native general linear
group, with the original rank hypotheses and signed matrix formulas.

## Implementation provenance

Adapted from `Quillen/Aglib/LinearAlgebra/Matrix/Bruhat/Decomposition.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Native elementary matrix units and
finite matrix stabilization are used directly.
-/

@[expose] public section

/-! ## BruhatExistence -/

section

noncomputable section
universe u
namespace Matrix.Bruhat
variable (F : Type u) [Field F]

/-- The last diagonal unit, with every old coordinate equal to one. -/
def lastDiagonal (n : ℕ) (a : Fˣ) : Matrix.GeneralLinearGroup (Fin (n + 1)) F :=
  monomialToGL F (n + 1) ⟨Fin.snoc 1 a, 1⟩

lemma mul_lastDiagonal_val {n : ℕ} (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F)
    (a : Fˣ) (i j : Fin (n + 1)) :
    (g * lastDiagonal F n a).val i j =
      g.val i j * ((Fin.snoc (1 : Fin n → Fˣ) a : Fin (n + 1) → Fˣ) j : F) := by
  change (g.val * monomialMatrix F (⟨Fin.snoc 1 a, 1⟩ : MonomialGroup F (n + 1))) i j = _
  rw [matrix_mul_monomial]
  rfl

lemma lastDiagonal_mul_val {n : ℕ} (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F)
    (a : Fˣ) (i j : Fin (n + 1)) :
    (lastDiagonal F n a * g).val i j =
      ((Fin.snoc (1 : Fin n → Fˣ) a : Fin (n + 1) → Fˣ) i : F) * g.val i j := by
  change (monomialMatrix F (⟨Fin.snoc 1 a, 1⟩ : MonomialGroup F (n + 1)) * g.val) i j = _
  rw [monomial_mul_matrix]
  rfl

lemma lastDiagonal_commute_step (n : ℕ) (a : Fˣ) (g : Matrix.GeneralLinearGroup (Fin n) F) :
    Commute (lastDiagonal F n a) (_root_.StableGeneralLinear.step F n g) := by
  apply Units.ext
  ext i j
  rw [lastDiagonal_mul_val, mul_lastDiagonal_val]
  cases i using Fin.lastCases <;> cases j using Fin.lastCases <;> simp

lemma isolated_eq_step_corner (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F)
    (hcol : ∀ i : Fin n, g.val i.castSucc (Fin.last n) = 0)
    (hrow : ∀ j : Fin n, g.val (Fin.last n) j.castSucc = 0)
    (a : Fˣ) (ha : (a : F) = g.val (Fin.last n) (Fin.last n)) :
    g = _root_.StableGeneralLinear.step F n (cornerUnit F n g hcol hrow) * lastDiagonal F n
      a := by
  apply Units.ext
  ext i j
  rw [mul_lastDiagonal_val]
  cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
    simp [hcol, hrow, ha, cornerUnit]

/-- Extend an actual monomial coordinate tuple with an arbitrary final diagonal unit. -/
def extendMonomialWithLast {n : ℕ} (m : MonomialGroup F n) (a : Fˣ) : MonomialGroup F (n + 1) :=
  ⟨Fin.snoc m.left a, permStabilize m.right⟩

lemma extendMonomialWithLast_toGL {n : ℕ} (m : MonomialGroup F n) (a : Fˣ) :
    monomialToGL F (n + 1) (extendMonomialWithLast F m a) =
      _root_.StableGeneralLinear.step F n (monomialToGL F n m) * lastDiagonal F n a := by
  apply Units.ext
  ext i j
  rw [mul_lastDiagonal_val]
  change (if i = permStabilize m.right j then
    ((Fin.snoc m.left a : Fin (n + 1) → Fˣ) i : F) else 0) = _
  cases i using Fin.lastCases <;> cases j using Fin.lastCases
  · simp
  · rename_i j
    simp only [permStabilize_castSucc,
      (Fin.castSucc_ne_last (m.right j)).symm, ↓reduceIte,
      _root_.StableGeneralLinear.step_val_last_castSucc,
      zero_mul]
  · simp
  · rw [_root_.StableGeneralLinear.step_val_castSucc]
    simp only [permStabilize_castSucc, Fin.castSucc_inj, Fin.snoc_castSucc,
      Pi.one_apply, Units.val_one, mul_one]
    rfl

/-- Every actual finite invertible matrix has an upper-unipotent/monomial/upper-unipotent
factorization, constructed by isolating the first nonzero last-row pivot. -/
theorem finite_bruhat_exists (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) F) :
    ∃ m : MonomialGroup F n, ∃ U V : upperUnipotent F n,
      g = (U : Matrix.GeneralLinearGroup (Fin n) F) * monomialToGL F n m * V := by
  induction n with
  | zero => exact ⟨1, 1, 1, Subsingleton.elim _ _⟩
  | succ n ih =>
    obtain ⟨c, U, V, hc, hrow, hcol⟩ := isolate_last_row_pivot F n g
    let ρ := pivotColumnEquiv c
    let P := permutationGL F (n + 1) ρ
    let C : Matrix.GeneralLinearGroup (Fin (n + 1)) F := (U :
      Matrix.GeneralLinearGroup (Fin (n + 1)) F) * g * V * P
    have hCcol (i : Fin n) : C.val i.castSucc (Fin.last n) = 0 := by
      change ((_ : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * permutationGL F (n + 1) ρ).val
        i.castSucc (Fin.last n) = 0
      rw [mul_permutationGL_val, pivotColumnEquiv_last, hcol]
      simp
    have hCrow (j : Fin n) : C.val (Fin.last n) j.castSucc = 0 := by
      change ((_ : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * permutationGL F (n + 1) ρ).val
        (Fin.last n) j.castSucc = 0
      rw [mul_permutationGL_val, pivotColumnEquiv_castSucc, hrow]
      simp
    let a := Units.mk0 (g.val (Fin.last n) c) hc
    have ha : (a : F) = C.val (Fin.last n) (Fin.last n) := by
      change g.val (Fin.last n) c =
        ((_ : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * permutationGL F (n + 1) ρ).val
          (Fin.last n) (Fin.last n)
      rw [mul_permutationGL_val, pivotColumnEquiv_last, hrow]
      simp
    let A := cornerUnit F n C hCcol hCrow
    obtain ⟨m, U₀, V₀, hA⟩ := ih A
    let U₁ : upperUnipotent F (n + 1) :=
      ⟨_root_.StableGeneralLinear.step F n U₀, upperUnipotent_step F n U₀⟩
    let V₁ : upperUnipotent F (n + 1) :=
      ⟨P * _root_.StableGeneralLinear.step F n V₀ * P⁻¹, upperUnipotent_pivot_conjugate F n
        c V₀⟩
    let m₁ : MonomialGroup F (n + 1) :=
      extendMonomialWithLast F m a * SemidirectProduct.inr ρ⁻¹
    have hC : C = (U₁ : Matrix.GeneralLinearGroup (Fin (n + 1)) F) *
        monomialToGL F (n + 1) (extendMonomialWithLast F m a) *
          _root_.StableGeneralLinear.step F n V₀ := by
      rw [isolated_eq_step_corner F n C hCcol hCrow a ha]
      change _root_.StableGeneralLinear.step F n A * lastDiagonal F n a = _
      rw [hA, map_mul, map_mul, extendMonomialWithLast_toGL]
      simp only [mul_assoc]
      rw [(lastDiagonal_commute_step F n a V₀).symm.eq]
    refine ⟨m₁, U⁻¹ * U₁, V₁ * V⁻¹, ?_⟩
    have he := congrArg (fun z : Matrix.GeneralLinearGroup (Fin (n + 1)) F =>
      (U : Matrix.GeneralLinearGroup (Fin (n + 1)) F)⁻¹ * z * P⁻¹ *
        (V : Matrix.GeneralLinearGroup (Fin (n + 1)) F)⁻¹) hC
    simpa [C, m₁, V₁, P, permutationGL, map_mul, map_inv, mul_assoc] using he

end Matrix.Bruhat

end

end

/-! ## BruhatProjection -/

section

noncomputable section
universe u
namespace Matrix.Bruhat
variable (F : Type u) [Field F]

/-- The actual finite matrix Bruhat projection to its unique monomial factor.
The definition chooses a proved decomposition; uniqueness removes dependence on that choice. -/
def bruhatMonomial (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) F) : MonomialGroup F n :=
  Classical.choose (finite_bruhat_exists F n g)

lemma bruhatMonomial_factorization (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) F) :
    ∃ U V : upperUnipotent F n,
      g = (U : Matrix.GeneralLinearGroup (Fin n) F) * monomialToGL F n (bruhatMonomial F n g)
        * V :=
  Classical.choose_spec (finite_bruhat_exists F n g)

lemma bruhatMonomial_eq_of_factorization (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) F)
    (m : MonomialGroup F n) (U V : upperUnipotent F n)
    (hg : g = (U : Matrix.GeneralLinearGroup (Fin n) F) * monomialToGL F n m * V) :
    bruhatMonomial F n g = m := by
  obtain ⟨U₀, V₀, h₀⟩ := bruhatMonomial_factorization F n g
  exact bruhat_monomial_unique F _ m U₀ V₀ U V (h₀.symm.trans hg)

@[simp] lemma bruhatMonomial_monomial (n : ℕ) (m : MonomialGroup F n) :
    bruhatMonomial F n (monomialToGL F n m) = m := by
  apply bruhatMonomial_eq_of_factorization F n _ m 1 1
  simp

@[simp] lemma bruhatMonomial_one (n : ℕ) : bruhatMonomial F n 1 = 1 := by
  simpa using bruhatMonomial_monomial F n 1

/-- Actual upper-unitriangular multiplication on either side preserves the factor. -/
theorem bruhatMonomial_unipotent_invariant (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) F)
    (U V : upperUnipotent F n) :
    bruhatMonomial F n ((U : Matrix.GeneralLinearGroup (Fin n) F) * g * V) = bruhatMonomial F
      n g := by
  obtain ⟨U₀, V₀, h₀⟩ := bruhatMonomial_factorization F n g
  apply bruhatMonomial_eq_of_factorization F n _ _ (U * U₀) (V₀ * V)
  nth_rw 1 [h₀]
  simp [mul_assoc]

/-- The literal diagonal matrices as a homomorphism. -/
def diagonalGL (n : ℕ) : (Fin n → Fˣ) →* Matrix.GeneralLinearGroup (Fin n) F :=
  (monomialToGL F n).comp SemidirectProduct.inl

lemma diagonalGL_conjugate_val {n : ℕ} (d : Fin n → Fˣ) (g : Matrix.GeneralLinearGroup (Fin n) F)
    (i j : Fin n) :
    (diagonalGL F n d * g * (diagonalGL F n d)⁻¹).val i j =
      (d i : F) * g.val i j * ((d j)⁻¹ : Fˣ) := by
  rw [← map_inv]
  change (monomialMatrix F (⟨d, 1⟩ : MonomialGroup F n) * g.val *
    monomialMatrix F (⟨d⁻¹, 1⟩ : MonomialGroup F n)) i j = _
  rw [matrix_mul_monomial, monomial_mul_matrix]
  rfl

lemma upperUnipotent_diagonal_conjugate (n : ℕ) (d : Fin n → Fˣ)
    (g : upperUnipotent F n) :
    diagonalGL F n d * g * (diagonalGL F n d)⁻¹ ∈ upperUnipotent F n := by
  constructor
  · intro i j hji
    rw [diagonalGL_conjugate_val, g.property.1 hji, mul_zero, zero_mul]
  · intro i
    rw [diagonalGL_conjugate_val, g.property.2 i, mul_one]
    exact Units.mul_inv (d i)

/-- The actual Bruhat projection is equivariant for left diagonal multiplication. -/
theorem bruhatMonomial_diagonal_left (n : ℕ) (d : Fin n → Fˣ)
    (g : Matrix.GeneralLinearGroup (Fin n) F) :
    bruhatMonomial F n (diagonalGL F n d * g) =
      SemidirectProduct.inl d * bruhatMonomial F n g := by
  obtain ⟨U, V, h⟩ := bruhatMonomial_factorization F n g
  let U₁ : upperUnipotent F n :=
    ⟨diagonalGL F n d * U * (diagonalGL F n d)⁻¹, upperUnipotent_diagonal_conjugate F n d U⟩
  apply bruhatMonomial_eq_of_factorization F n _ _ U₁ V
  nth_rw 1 [h]
  rw [map_mul]
  change _ = (diagonalGL F n d * U * (diagonalGL F n d)⁻¹) *
    (diagonalGL F n d * monomialToGL F n (bruhatMonomial F n g)) * V
  simp [mul_assoc]

/-- The actual Bruhat projection is equivariant for right diagonal multiplication. -/
theorem bruhatMonomial_diagonal_right (n : ℕ) (d : Fin n → Fˣ)
    (g : Matrix.GeneralLinearGroup (Fin n) F) :
    bruhatMonomial F n (g * diagonalGL F n d) =
      bruhatMonomial F n g * SemidirectProduct.inl d := by
  obtain ⟨U, V, h⟩ := bruhatMonomial_factorization F n g
  let V₁ : upperUnipotent F n :=
    ⟨diagonalGL F n d⁻¹ * V * (diagonalGL F n d⁻¹)⁻¹,
      upperUnipotent_diagonal_conjugate F n d⁻¹ V⟩
  apply bruhatMonomial_eq_of_factorization F n _ _ U V₁
  nth_rw 1 [h]
  rw [map_mul]
  change _ = (U : Matrix.GeneralLinearGroup (Fin n) F) *
    (monomialToGL F n (bruhatMonomial F n g) * diagonalGL F n d) *
      (diagonalGL F n d⁻¹ * V * (diagonalGL F n d⁻¹)⁻¹)
  rw [map_inv, inv_inv]
  simp [mul_assoc]

end Matrix.Bruhat

end

end

/-! ## BruhatSimpleRoot -/

section

noncomputable section
universe u
namespace Matrix.Bruhat
variable (F : Type u) [Field F]

lemma elementary_mem_upper {n : ℕ} (i j : Fin n) (hij : i < j) (a : F) :
    Matrix.GeneralLinearGroup.elementary i j (ne_of_lt hij) a ∈ upperUnipotent F n := by
  constructor
  · change (1 + Matrix.single i j a).IsUpperTriangular
    exact Matrix.blockTriangular_one.add (Matrix.blockTriangular_single (b := id) hij.le a)
  · intro k
    by_cases hk : k = i
    · subst k
      simp [Matrix.GeneralLinearGroup.elementary_val,
        Matrix.single, hij.ne.symm]
    · simp [Matrix.GeneralLinearGroup.elementary_val,
      Matrix.single, Ne.symm hk]

/-- An actual simple upper root as an element of the upper-unitriangular group. -/
def simpleUpper (n : ℕ) (i : Fin n) (a : F) : upperUnipotent F (n + 1) :=
  ⟨Matrix.GeneralLinearGroup.elementary i.castSucc i.succ i.castSucc_lt_succ.ne a,
    elementary_mem_upper F i.castSucc i.succ i.castSucc_lt_succ a⟩

lemma upper_adjacent_mul (n : ℕ) (U V : upperUnipotent F (n + 1)) (i : Fin n) :
    ((U * V : upperUnipotent F (n + 1)) : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val
        i.castSucc i.succ =
      (U : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val i.castSucc i.succ +
        (V : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val i.castSucc i.succ := by
  have hij : i.castSucc ≠ i.succ := i.castSucc_lt_succ.ne
  change (∑ k : Fin (n + 1), (U : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val i.castSucc k
    *
      (V : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val k i.succ) = _
  calc
    _ = ∑ k : Fin (n + 1),
        ((if k = i.castSucc then (V : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val
          i.castSucc i.succ
          else 0) +
        (if k = i.succ then (U : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val i.castSucc
          i.succ
          else 0)) := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k = i.castSucc
      · subst k
        simp [U.property.2, hij]
      · by_cases hk' : k = i.succ
        · subst k
          simp [V.property.2, hij.symm]
        · have hcases : k < i.castSucc ∨ i.succ < k := by
            have hkval : k.val ≠ i.val := fun he => hk (Fin.ext he)
            have hkval' : k.val ≠ i.val + 1 := fun he => hk' (Fin.ext he)
            change k.val < i.val ∨ i.val + 1 < k.val
            omega
          rcases hcases with hlt | hgt
          · have hz : (U : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val i.castSucc k = 0 :=
              U.property.1 hlt
            simp [hz, hk, hk']
          · have hz : (V : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val k i.succ = 0 :=
              V.property.1 hgt
            simp [hz, hk, hk']
    _ = _ := by simp [Finset.sum_add_distrib, add_comm]

@[simp] lemma simpleUpper_entry (n : ℕ) (i : Fin n) (a : F) :
    (simpleUpper F n i a : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val i.castSucc i.succ =
      a := by
  have hij : i.castSucc ≠ i.succ := i.castSucc_lt_succ.ne
  simp [simpleUpper, Matrix.GeneralLinearGroup.elementary_val,
    Matrix.single, hij]

/-- Split the actual simple entry off an arbitrary upper-unitriangular matrix. -/
lemma split_simple_upper (n : ℕ) (i : Fin n) (U : upperUnipotent F (n + 1)) :
    ∃ U₀ : upperUnipotent F (n + 1),
      (U₀ : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val i.castSucc i.succ = 0 ∧
      U = U₀ * simpleUpper F n i
        ((U : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val i.castSucc i.succ) := by
  let t := (U : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val i.castSucc i.succ
  refine ⟨U * simpleUpper F n i (-t), ?_, ?_⟩
  · rw [upper_adjacent_mul, simpleUpper_entry]
    exact add_neg_cancel t
  · apply Subtype.ext
    change (U : Matrix.GeneralLinearGroup (Fin (n + 1)) F) =
      (U : Matrix.GeneralLinearGroup (Fin (n + 1)) F) *
        Matrix.GeneralLinearGroup.elementary i.castSucc i.succ i.castSucc_lt_succ.ne (-t) *
          Matrix.GeneralLinearGroup.elementary i.castSucc i.succ i.castSucc_lt_succ.ne t
    rw [mul_assoc, Matrix.GeneralLinearGroup.elementary_mul_same, neg_add_cancel,
      Matrix.GeneralLinearGroup.elementary_zero, mul_one]

lemma monomialToGL_factor (n : ℕ) (m : MonomialGroup F n) :
    monomialToGL F n m = diagonalGL F n m.left * permutationGL F n m.right := by
  have he := congrArg (monomialToGL F n) (SemidirectProduct.inl_left_mul_inr_right m)
  exact (map_mul _ _ _).symm.trans he |>.symm

/-- Monomial conjugation on the literal matrix entries. -/
lemma monomial_conjugate_val {n : ℕ} (m : MonomialGroup F n)
    (g : Matrix.GeneralLinearGroup (Fin n) F) (i j : Fin n) :
    (monomialToGL F n m * g * (monomialToGL F n m)⁻¹).val i j =
      (m.left i : F) * g.val (m.right.symm i) (m.right.symm j) * ((m.left j)⁻¹ : Fˣ) := by
  have he : monomialToGL F n m * g * (monomialToGL F n m)⁻¹ =
      diagonalGL F n m.left *
        (permutationGL F n m.right * g * (permutationGL F n m.right)⁻¹) *
          (diagonalGL F n m.left)⁻¹ := by
    rw [monomialToGL_factor, _root_.mul_inv_rev]
    simp [mul_assoc]
  rw [he, diagonalGL_conjugate_val, permutationGL_conjugate_val]

private lemma simpleSwap_order {n : ℕ} (i : Fin n) (r s : Fin (n + 1)) (hsr : s < r) :
    Equiv.swap i.castSucc i.succ s < Equiv.swap i.castSucc i.succ r ∨
      (r = i.succ ∧ s = i.castSucc) := by
  by_cases hr₀ : r = i.castSucc
  · subst r
    left
    have hs₁ : s ≠ i.succ := (hsr.trans i.castSucc_lt_succ).ne
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hsr.ne hs₁]
    exact hsr.trans i.castSucc_lt_succ
  by_cases hr₁ : r = i.succ
  · subst r
    by_cases hs₀ : s = i.castSucc
    · exact Or.inr ⟨rfl, hs₀⟩
    · left
      rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hs₀ hsr.ne]
      exact lt_of_le_of_ne (Fin.le_castSucc_iff.mpr hsr) hs₀
  have hfixr := Equiv.swap_apply_of_ne_of_ne hr₀ hr₁
  by_cases hs₀ : s = i.castSucc
  · subst s
    left
    rw [Equiv.swap_apply_left, hfixr]
    exact lt_of_le_of_ne (Fin.castSucc_lt_iff_succ_le.mp hsr) (Ne.symm hr₁)
  by_cases hs₁ : s = i.succ
  · subst s
    left
    rw [Equiv.swap_apply_right, hfixr]
    exact i.castSucc_lt_succ.trans hsr
  left
  rw [hfixr, Equiv.swap_apply_of_ne_of_ne hs₀ hs₁]
  exact hsr

/-- A simple reflection normalizes the upper subgroup with its one simple entry removed. -/
lemma upper_simple_reflection_conjugate (n : ℕ) (i : Fin n) (d : Fin (n + 1) → Fˣ)
    (U : upperUnipotent F (n + 1))
    (hU : (U : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val i.castSucc i.succ = 0) :
    let m : MonomialGroup F (n + 1) := ⟨d, Equiv.swap i.castSucc i.succ⟩
    monomialToGL F (n + 1) m * U * (monomialToGL F (n + 1) m)⁻¹ ∈
      upperUnipotent F (n + 1) := by
  dsimp only
  constructor
  · intro r s hsr
    change s < r at hsr
    rw [monomial_conjugate_val]
    have hz : (U : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val
        (Equiv.swap i.castSucc i.succ r) (Equiv.swap i.castSucc i.succ s) = 0 := by
      rcases simpleSwap_order i r s hsr with hlt | ⟨rfl, rfl⟩
      · exact U.property.1 hlt
      · simpa using hU
    change (d r : F) * (U : Matrix.GeneralLinearGroup (Fin (n + 1)) F).val
      (Equiv.swap i.castSucc i.succ r) (Equiv.swap i.castSucc i.succ s) *
        ((d s)⁻¹ : Fˣ) = 0
    rw [hz, mul_zero, zero_mul]
  · intro r
    rw [monomial_conjugate_val, U.property.2, mul_one]
    exact Units.mul_inv (d r)

end Matrix.Bruhat

end

end
