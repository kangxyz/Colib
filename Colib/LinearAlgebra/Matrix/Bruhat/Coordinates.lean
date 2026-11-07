/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, kangxyz
-/
module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Fin.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Block
public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.Stabilization

/-!
# Coordinates

Finite matrix Bruhat coordinates over fields, using the native general linear
group, with the original rank hypotheses and signed matrix formulas.

## Implementation provenance

Adapted from `Quillen/Aglib/LinearAlgebra/Matrix/Bruhat/Coordinates.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Native elementary matrix units and
finite matrix stabilization are used directly.
-/

@[expose] public section

/-! ## MonomialExtension -/

section

noncomputable section
universe u
namespace Matrix.Bruhat
variable (F : Type u) [Field F]

/-- Permute literal diagonal entries. -/
def permDiagonal {n : ℕ} (σ : Equiv.Perm (Fin n)) (d : Fin n → Fˣ) : Fin n → Fˣ :=
  fun i => d (σ.symm i)

end Matrix.Bruhat

end

end

/-! ## MonomialProjection -/

section

noncomputable section
universe u
namespace Matrix.Bruhat
variable (F : Type u) [Field F]

/-- The ordinary action of a permutation on diagonal entries. -/
def diagonalPermAut {n : ℕ} (σ : Equiv.Perm (Fin n)) : MulAut (Fin n → Fˣ) where
  toFun := permDiagonal F σ
  invFun := permDiagonal F σ⁻¹
  left_inv d := by
    funext i
    change d (σ.symm (σ i)) = d i
    rw [σ.symm_apply_apply]
  right_inv d := by
    funext i
    change d (σ (σ.symm i)) = d i
    rw [σ.apply_symm_apply]
  map_mul' _ _ := rfl

/-- The ordinary permutation action as a group homomorphism. -/
def diagonalPermAction (n : ℕ) : Equiv.Perm (Fin n) →* MulAut (Fin n → Fˣ) where
  toFun := diagonalPermAut F
  map_one' := MulEquiv.ext (fun _ => rfl)
  map_mul' _ _ := MulEquiv.ext (fun _ => rfl)

/-- Literal diagonal and permutation coordinates for finite monomial matrices. -/
abbrev MonomialGroup (n : ℕ) :=
  SemidirectProduct (Fin n → Fˣ) (Equiv.Perm (Fin n)) (diagonalPermAction F n)

end Matrix.Bruhat

end

end

/-! ## MonomialStabilization -/

section

noncomputable section
universe u
namespace Matrix.Bruhat
variable (F : Type u) [Field F]

/-- Fix the new final index and retain the original permutation on all old indices. -/
def permStabilize {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) where
  toFun := Fin.lastCases (Fin.last n) (fun i => (σ i).castSucc)
  invFun := Fin.lastCases (Fin.last n) (fun i => (σ.symm i).castSucc)
  left_inv i := by refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  right_inv i := by refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

@[simp] lemma permStabilize_castSucc {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permStabilize σ i.castSucc = (σ i).castSucc := by simp [permStabilize]

@[simp] lemma permStabilize_last {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    permStabilize σ (Fin.last n) = Fin.last n := by simp [permStabilize]

end Matrix.Bruhat

end

end

/-! ## MonomialMatrices -/

section

noncomputable section
universe u
namespace Matrix.Bruhat
variable (F : Type u) [Field F]

/-- The literal finite matrix represented by diagonal and permutation coordinates. -/
def monomialMatrix {n : ℕ} (x : MonomialGroup F n) : Matrix (Fin n) (Fin n) F :=
  fun i j => if i = x.right j then x.left i else 0

lemma monomialMatrix_mul {n : ℕ} (x y : MonomialGroup F n) :
    monomialMatrix F (x * y) = monomialMatrix F x * monomialMatrix F y := by
  ext i j
  change (if i = x.right (y.right j) then
    (x.left i : F) * (y.left (x.right.symm i) : F) else 0) =
      ∑ k : Fin n, (if i = x.right k then (x.left i : F) else 0) *
        (if k = y.right j then (y.left k : F) else 0)
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  by_cases h : i = x.right (y.right j)
  · subst i
    simp
  · simp [h]

lemma monomialMatrix_one (n : ℕ) : monomialMatrix F (1 : MonomialGroup F n) = 1 := by
  ext i j
  simp only [monomialMatrix, SemidirectProduct.one_right, Equiv.Perm.one_apply,
    SemidirectProduct.one_left, Pi.one_apply, Units.val_one, Matrix.one_apply]
  rfl

/-- The actual matrix homomorphism, with its group law proved entry by entry. -/
def monomialMatrixHom (n : ℕ) : MonomialGroup F n →* Matrix (Fin n) (Fin n) F where
  toFun := monomialMatrix F
  map_one' := monomialMatrix_one F n
  map_mul' := monomialMatrix_mul F

/-- The same matrices as units in the actual finite matrix ring. -/
def monomialToGL (n : ℕ) : MonomialGroup F n →* Matrix.GeneralLinearGroup (Fin n) F :=
  (monomialMatrixHom F n).toHomUnits

lemma monomialMatrix_injective (n : ℕ) : Function.Injective (@monomialMatrix F _ n) := by
  intro x y h
  have hs : x.right = y.right := by
    apply Equiv.ext
    intro j
    have he := congrFun (congrFun h (x.right j)) j
    change (if x.right j = x.right j then (x.left (x.right j) : F) else 0) =
      (if x.right j = y.right j then (y.left (x.right j) : F) else 0) at he
    by_contra hn
    simp only [↓reduceIte, hn] at he
    exact (x.left (x.right j)).ne_zero he
  have hd : x.left = y.left := by
    funext i
    apply Units.ext
    have he := congrFun (congrFun h i) (x.right.symm i)
    simpa [monomialMatrix, ← hs] using he
  exact SemidirectProduct.ext hd hs

lemma monomialToGL_injective (n : ℕ) : Function.Injective (monomialToGL F n) := by
  intro x y h
  exact monomialMatrix_injective F n (congrArg Units.val h)

end Matrix.Bruhat

end

end

/-! ## BruhatUniqueness -/

section

noncomputable section
universe u
namespace Matrix.Bruhat
variable (F : Type u) [Field F]

lemma perm_eq_one_of_apply_le {n : ℕ} (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i, σ i ≤ i) : σ = 1 := by
  apply Equiv.ext
  intro i
  by_contra h
  have ht : (σ i).val < i.val := lt_of_le_of_ne (hσ i) (fun hh => h (Fin.ext hh))
  have hs : (∑ j : Fin n, (σ j).val) < ∑ j : Fin n, j.val :=
    Finset.sum_lt_sum (fun j _ => hσ j) ⟨i, Finset.mem_univ i, ht⟩
  have he := Equiv.sum_comp σ (fun j : Fin n => j.val)
  omega

lemma matrix_mul_monomial {n : ℕ} (U : Matrix (Fin n) (Fin n) F)
    (x : MonomialGroup F n) (i j : Fin n) :
    (U * monomialMatrix F x) i j = U i (x.right j) * (x.left (x.right j) : F) := by
  simp [Matrix.mul_apply, monomialMatrix, mul_ite]

lemma monomial_mul_matrix {n : ℕ} (x : MonomialGroup F n)
    (U : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    (monomialMatrix F x * U) i j = (x.left i : F) * U (x.right.symm i) j := by
  have hi (k : Fin n) : i = x.right k ↔ k = x.right.symm i := by
    constructor
    · intro h
      exact (Equiv.eq_symm_apply x.right).2 h.symm
    · intro h
      exact ((Equiv.eq_symm_apply x.right).1 h).symm
  simp [Matrix.mul_apply, monomialMatrix, hi, ite_mul]

/-- Monomial factors cannot change across an upper-unipotent equality.
The proof uses the original finite matrix entries, not equality in any presentation quotient. -/
theorem monomial_unique_of_upper_unipotent {n : ℕ}
    (x y : MonomialGroup F n) (U V : Matrix (Fin n) (Fin n) F)
    (hU : ∀ i, U i i = 1) (hV : V.IsUpperTriangular) (hVdiag : ∀ i, V i i = 1)
    (he : U * monomialMatrix F x = monomialMatrix F y * V) : x = y := by
  have hle (j : Fin n) : y.right.symm (x.right j) ≤ j := by
    have hentry := congrFun (congrFun he (x.right j)) j
    rw [matrix_mul_monomial, monomial_mul_matrix, hU, one_mul] at hentry
    by_contra hn
    rw [hV (lt_of_not_ge hn), mul_zero] at hentry
    exact (x.left (x.right j)).ne_zero hentry
  have hs : x.right = y.right := by
    have hθ : y.right⁻¹ * x.right = 1 := perm_eq_one_of_apply_le _ hle
    exact (inv_mul_eq_one.mp hθ).symm
  have hd : x.left = y.left := by
    funext i
    apply Units.ext
    have hentry := congrFun (congrFun he i) (x.right.symm i)
    rw [matrix_mul_monomial, monomial_mul_matrix, x.right.apply_symm_apply,
      hU, one_mul, ← hs, hVdiag, mul_one] at hentry
    exact hentry
  exact SemidirectProduct.ext hd hs

end Matrix.Bruhat

end

end

/-! ## UpperUnipotent -/

section

noncomputable section
universe u
namespace Matrix.Bruhat
variable (F : Type u) [Field F]

lemma upper_mul_diagonal {n : ℕ} (A B : Matrix (Fin n) (Fin n) F)
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hj | hj
    · rw [hA hj, zero_mul]
    · rw [hB hj, mul_zero]
  · simp

/-- The actual finite upper-unitriangular subgroup of matrix units. -/
def upperUnipotent (n : ℕ) : Subgroup (Matrix.GeneralLinearGroup (Fin n) F) where
  carrier := {g | g.val.IsUpperTriangular ∧ ∀ i, g.val i i = 1}
  one_mem' := ⟨Matrix.blockTriangular_one, fun _ => Matrix.one_apply_eq _⟩
  mul_mem' hg hh := ⟨hg.1.mul hh.1, fun i => by
    rw [Units.val_mul, upper_mul_diagonal F _ _ hg.1 hh.1 i, hg.2 i, hh.2 i, one_mul]⟩
  inv_mem' {g} hg := by
    have hInv : (g⁻¹).val.IsUpperTriangular := by
      let := g.invertible
      rw [Matrix.GeneralLinearGroup.coe_inv]
      exact Matrix.blockTriangular_inv_of_blockTriangular hg.1
    refine ⟨hInv, fun i => ?_⟩
    have he := congrFun (congrFun (congrArg
      (fun z : Matrix.GeneralLinearGroup (Fin n) F => z.val) (mul_inv_cancel g)) i) i
    change (g.val * (g⁻¹).val) i i = (1 : Matrix (Fin n) (Fin n) F) i i at he
    rw [upper_mul_diagonal F _ _ hg.1 hInv i, hg.2 i, one_mul, Matrix.one_apply_eq] at he
    exact he

lemma upperUnipotent_triangular {n : ℕ} (g : upperUnipotent F n) :
    (g : Matrix.GeneralLinearGroup (Fin n) F).val.IsUpperTriangular := g.property.1

lemma upperUnipotent_diagonal {n : ℕ} (g : upperUnipotent F n) (i : Fin n) :
    (g : Matrix.GeneralLinearGroup (Fin n) F).val i i = 1 := g.property.2 i

/-- The finite Bruhat monomial factor is unique whenever both decompositions exist. -/
theorem bruhat_monomial_unique {n : ℕ} (x y : MonomialGroup F n)
    (U V U' V' : upperUnipotent F n)
    (he : (U : Matrix.GeneralLinearGroup (Fin n) F) * monomialToGL F n x * V =
      (U' : Matrix.GeneralLinearGroup (Fin n) F) * monomialToGL F n y * V') : x = y := by
  have hm : ((U'⁻¹ * U : upperUnipotent F n) : Matrix.GeneralLinearGroup (Fin n) F) *
      monomialToGL F n x = monomialToGL F n y *
        ((V' * V⁻¹ : upperUnipotent F n) : Matrix.GeneralLinearGroup (Fin n) F) := by
    have h := congrArg (fun z : Matrix.GeneralLinearGroup (Fin n) F => (U' :
      Matrix.GeneralLinearGroup (Fin n) F)⁻¹ *
      z * (V : Matrix.GeneralLinearGroup (Fin n) F)⁻¹) he
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, inv_mul_cancel_left,
      mul_inv_cancel_right, mul_inv_cancel, mul_one] using h
  exact monomial_unique_of_upper_unipotent F x y _ _
    (upperUnipotent_diagonal F (U'⁻¹ * U))
    (upperUnipotent_triangular F (V' * V⁻¹))
    (upperUnipotent_diagonal F (V' * V⁻¹))
      (congrArg (fun z : Matrix.GeneralLinearGroup (Fin n) F => z.val) hm)

end Matrix.Bruhat

end

end

/-! ## BruhatShears -/

section

noncomputable section
universe u
namespace Matrix.Bruhat
open scoped Matrix
variable (F : Type u) [Field F]

/-- The rank-one square-zero shear as an actual matrix unit. -/
def shearUnit {n : ℕ} (v w : Fin n → F) (hvw : w ⬝ᵥ v = 0) :
    Matrix.GeneralLinearGroup (Fin n) F where
  val := 1 + Matrix.vecMulVec v w
  inv := 1 - Matrix.vecMulVec v w
  val_inv := by
    have hsq : Matrix.vecMulVec v w * Matrix.vecMulVec v w = 0 := by
      rw [Matrix.vecMulVec_mul_vecMulVec, hvw, zero_smul, Matrix.vecMulVec_zero]
    simp [mul_sub, add_mul, hsq]
  inv_val := by
    have hsq : Matrix.vecMulVec v w * Matrix.vecMulVec v w = 0 := by
      rw [Matrix.vecMulVec_mul_vecMulVec, hvw, zero_smul, Matrix.vecMulVec_zero]
    simp [sub_mul, mul_add, hsq]

/-- Add multiples of row `k` to the other rows. -/
def columnShear {n : ℕ} (k : Fin n) (v : Fin n → F) (hv : v k = 0) :
    Matrix.GeneralLinearGroup (Fin n) F :=
  shearUnit F v (Pi.single k 1) (by simpa using hv)

/-- Add multiples of column `k` to the other columns. -/
def rowShear {n : ℕ} (k : Fin n) (w : Fin n → F) (hw : w k = 0) :
    Matrix.GeneralLinearGroup (Fin n) F :=
  shearUnit F (Pi.single k 1) w (by simpa using hw)

lemma columnShear_mul_apply {n : ℕ} (k : Fin n) (v : Fin n → F) (hv : v k = 0)
    (A : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    ((columnShear F k v hv).val * A) i j = A i j + v i * A k j := by
  change ((1 + Matrix.vecMulVec v (Pi.single k 1)) * A) i j = _
  rw [add_mul, one_mul, Matrix.vecMulVec_mul]
  simp [Matrix.vecMulVec, Matrix.vecMul, dotProduct, Pi.single_apply]

lemma mul_rowShear_apply {n : ℕ} (k : Fin n) (w : Fin n → F) (hw : w k = 0)
    (A : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    (A * (rowShear F k w hw).val) i j = A i j + A i k * w j := by
  change (A * (1 + Matrix.vecMulVec (Pi.single k 1) w)) i j = _
  rw [mul_add, mul_one, Matrix.mul_vecMulVec]
  simp [Matrix.vecMulVec, Matrix.mulVec, dotProduct, Pi.single_apply]

lemma columnShear_mem_upper {n : ℕ} (k : Fin n) (v : Fin n → F)
    (hv : ∀ i, k ≤ i → v i = 0) : columnShear F k v (hv k le_rfl) ∈ upperUnipotent F n := by
  constructor
  · intro i j hji
    change j < i at hji
    change (1 : Matrix (Fin n) (Fin n) F) i j + v i * (Pi.single k (1 : F) : Fin n → F) j = 0
    by_cases hj : j = k
    · subst j
      simp [ne_of_gt hji, hv i (le_of_lt hji)]
    · simp [ne_of_gt hji, hj]
  · intro i
    change (1 : Matrix (Fin n) (Fin n) F) i i + v i * (Pi.single k (1 : F) : Fin n → F) i = 1
    by_cases hi : i = k
    · subst i
      simp [hv k le_rfl]
    · simp [hi]

lemma rowShear_mem_upper {n : ℕ} (k : Fin n) (w : Fin n → F)
    (hw : ∀ j, j ≤ k → w j = 0) : rowShear F k w (hw k le_rfl) ∈ upperUnipotent F n := by
  constructor
  · intro i j hji
    change j < i at hji
    change (1 : Matrix (Fin n) (Fin n) F) i j + (Pi.single k (1 : F) : Fin n → F) i * w j = 0
    by_cases hi : i = k
    · subst i
      simp [ne_of_gt hji, hw j (le_of_lt hji)]
    · simp [ne_of_gt hji, hi]
  · intro i
    change (1 : Matrix (Fin n) (Fin n) F) i i + (Pi.single k (1 : F) : Fin n → F) i * w i = 1
    by_cases hi : i = k
    · subst i
      simp [hw k le_rfl]
    · simp [hi]

end Matrix.Bruhat

end

end

/-! ## BruhatPivot -/

section

noncomputable section
universe u
namespace Matrix.Bruhat
open scoped Matrix
variable (F : Type u) [Field F]

lemma last_row_nonzero (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    ∃ j, g.val (Fin.last n) j ≠ 0 := by
  by_contra! hz
  have he := congrFun (congrFun g.val_inv (Fin.last n)) (Fin.last n)
  simp [Matrix.mul_apply, hz] at he

lemma last_row_first_pivot (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    ∃ c : Fin (n + 1), g.val (Fin.last n) c ≠ 0 ∧
      ∀ j, j < c → g.val (Fin.last n) j = 0 := by
  classical
  let s := Finset.univ.filter (fun j => g.val (Fin.last n) j ≠ 0)
  have hs : s.Nonempty := by
    obtain ⟨j, hj⟩ := last_row_nonzero F n g
    exact ⟨j, by simp [s, hj]⟩
  refine ⟨s.min' hs, (Finset.mem_filter.mp (Finset.min'_mem s hs)).2, ?_⟩
  intro j hj
  by_contra hn
  have hm : j ∈ s := by simp [s, hn]
  exact (not_le_of_gt hj) (Finset.min'_le s j hm)

/-- Genuine finite pivot elimination by upper-unitriangular row and column operations.
Both multipliers are actual matrix units; the isolated pivot remains the original field entry. -/
theorem isolate_last_row_pivot (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    ∃ c : Fin (n + 1), ∃ U V : upperUnipotent F (n + 1),
      g.val (Fin.last n) c ≠ 0 ∧
      (∀ j, (((U : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * g * V).val) (Fin.last n) j =
        if j = c then g.val (Fin.last n) c else 0) ∧
      (∀ i, (((U : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * g * V).val) i c =
        if i = Fin.last n then g.val (Fin.last n) c else 0) := by
  obtain ⟨c, hc, hbefore⟩ := last_row_first_pivot F n g
  let u : Fin (n + 1) → F := fun i =>
    if i = Fin.last n then 0 else -g.val i c / g.val (Fin.last n) c
  let v : Fin (n + 1) → F := fun j =>
    if c < j then -g.val (Fin.last n) j / g.val (Fin.last n) c else 0
  have hu (i : Fin (n + 1)) (hi : Fin.last n ≤ i) : u i = 0 := by
    have he : i = Fin.last n := le_antisymm (Fin.le_last i) hi
    simp [u, he]
  have hv (j : Fin (n + 1)) (hj : j ≤ c) : v j = 0 := by
    simp [v, not_lt_of_ge hj]
  let U : upperUnipotent F (n + 1) :=
    ⟨columnShear F (Fin.last n) u (hu _ le_rfl), columnShear_mem_upper F _ _ hu⟩
  let V : upperUnipotent F (n + 1) :=
    ⟨rowShear F c v (hv _ le_rfl), rowShear_mem_upper F _ _ hv⟩
  refine ⟨c, U, V, hc, ?_, ?_⟩
  · intro j
    change ((columnShear F (Fin.last n) u (hu _ le_rfl)).val * g.val *
      (rowShear F c v (hv _ le_rfl)).val) (Fin.last n) j = _
    rw [Matrix.mul_assoc, columnShear_mul_apply, hu _ le_rfl, zero_mul, add_zero,
      mul_rowShear_apply]
    by_cases hj : j = c
    · subst j
      simp [v]
    · rcases lt_or_gt_of_ne hj with hlt | hgt
      · rw [hbefore j hlt]
        simp [v, not_lt_of_gt hlt, hj]
      · simp only [v, hgt, ↓reduceIte, hj]
        field_simp
        ring
  · intro i
    change ((columnShear F (Fin.last n) u (hu _ le_rfl)).val * g.val *
      (rowShear F c v (hv _ le_rfl)).val) i c = _
    rw [mul_rowShear_apply, hv c le_rfl, mul_zero, add_zero, columnShear_mul_apply]
    by_cases hi : i = Fin.last n
    · subst i
      simp [u]
    · simp only [u, hi, ↓reduceIte]
      field_simp
      ring

end Matrix.Bruhat

end

end

/-! ## BruhatBlock -/

section

noncomputable section
universe u
namespace Matrix.Bruhat
variable (F : Type u) [Field F]

/-- The literal permutation matrix as an invertible finite matrix. -/
def permutationGL (n : ℕ) : Equiv.Perm (Fin n) →* Matrix.GeneralLinearGroup (Fin n) F :=
  (monomialToGL F n).comp SemidirectProduct.inr

lemma mul_permutationGL_val {n : ℕ} (g : Matrix.GeneralLinearGroup (Fin n) F)
    (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    (g * permutationGL F n σ).val i j = g.val i (σ j) := by
  change (g.val * monomialMatrix F (⟨1, σ⟩ : MonomialGroup F n)) i j = _
  rw [matrix_mul_monomial]
  simp

lemma permutationGL_mul_val {n : ℕ} (σ : Equiv.Perm (Fin n))
    (g : Matrix.GeneralLinearGroup (Fin n) F) (i j : Fin n) :
    (permutationGL F n σ * g).val i j = g.val (σ.symm i) j := by
  change (monomialMatrix F (⟨1, σ⟩ : MonomialGroup F n) * g.val) i j = _
  rw [monomial_mul_matrix]
  simp

lemma permutationGL_conjugate_val {n : ℕ} (σ : Equiv.Perm (Fin n))
    (g : Matrix.GeneralLinearGroup (Fin n) F) (i j : Fin n) :
    (permutationGL F n σ * g * (permutationGL F n σ)⁻¹).val i j =
      g.val (σ.symm i) (σ.symm j) := by
  rw [← map_inv, mul_permutationGL_val, permutationGL_mul_val]
  rfl

/-- Move the selected pivot column to the final position; retain the order of its complement. -/
def pivotColumnEquiv {n : ℕ} (c : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) :=
  finSuccEquivLast.trans (finSuccEquiv' c).symm

@[simp] lemma pivotColumnEquiv_castSucc {n : ℕ} (c : Fin (n + 1)) (i : Fin n) :
    pivotColumnEquiv c i.castSucc = c.succAbove i := by simp [pivotColumnEquiv]

@[simp] lemma pivotColumnEquiv_last {n : ℕ} (c : Fin (n + 1)) :
    pivotColumnEquiv c (Fin.last n) = c := by simp [pivotColumnEquiv]

@[simp] lemma pivotColumnEquiv_symm_succAbove {n : ℕ} (c : Fin (n + 1)) (i : Fin n) :
    (pivotColumnEquiv c).symm (c.succAbove i) = i.castSucc := by simp [pivotColumnEquiv]

@[simp] lemma pivotColumnEquiv_symm_self {n : ℕ} (c : Fin (n + 1)) :
    (pivotColumnEquiv c).symm c = Fin.last n := by simp [pivotColumnEquiv]

/-- An isolated last row/column gives an actual unit in the smaller finite matrix ring. -/
def cornerUnit (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F)
    (hcol : ∀ i : Fin n, g.val i.castSucc (Fin.last n) = 0)
    (hrow : ∀ j : Fin n, g.val (Fin.last n) j.castSucc = 0) :
    Matrix.GeneralLinearGroup (Fin n) F where
  val := g.val.submatrix Fin.castSucc Fin.castSucc
  inv := g.inv.submatrix Fin.castSucc Fin.castSucc
  val_inv := by
    ext i j
    have he := congrFun (congrFun g.val_inv i.castSucc) j.castSucc
    simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, hcol i, zero_mul, add_zero] at he
    simpa [Matrix.mul_apply, Matrix.one_apply] using he
  inv_val := by
    ext i j
    have he := congrFun (congrFun g.inv_val i.castSucc) j.castSucc
    simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, hrow j, mul_zero, add_zero] at he
    simpa [Matrix.mul_apply, Matrix.one_apply] using he

lemma upperUnipotent_step (n : ℕ) (g : upperUnipotent F n) :
    _root_.StableGeneralLinear.step F n g ∈ upperUnipotent F (n + 1) := by
  constructor
  · intro i j hji
    change j < i at hji
    cases i using Fin.lastCases <;> cases j using Fin.lastCases
    · exact False.elim (lt_irrefl _ hji)
    · exact _root_.StableGeneralLinear.step_val_last_castSucc F n g _
    · exact False.elim (not_lt_of_ge (Fin.le_last _) hji)
    · rw [_root_.StableGeneralLinear.step_val_castSucc]
      exact g.property.1 hji
  · intro i
    cases i using Fin.lastCases
    · exact _root_.StableGeneralLinear.step_val_last F n g
    · rw [_root_.StableGeneralLinear.step_val_castSucc]
      exact g.property.2 _

/-- The order-preserving complement embedding retains upper unitriangularity. -/
lemma upperUnipotent_pivot_conjugate (n : ℕ) (c : Fin (n + 1)) (g : upperUnipotent F n) :
    permutationGL F (n + 1) (pivotColumnEquiv c) * _root_.StableGeneralLinear.step F n g *
      (permutationGL F (n + 1) (pivotColumnEquiv c))⁻¹ ∈ upperUnipotent F (n + 1) := by
  constructor
  · intro i j hji
    change j < i at hji
    rw [permutationGL_conjugate_val]
    cases i using Fin.succAboveCases c <;> cases j using Fin.succAboveCases c
    · exact False.elim (lt_irrefl _ hji)
    · rw [pivotColumnEquiv_symm_self, pivotColumnEquiv_symm_succAbove,
        _root_.StableGeneralLinear.step_val_last_castSucc]
    · rw [pivotColumnEquiv_symm_self, pivotColumnEquiv_symm_succAbove,
        _root_.StableGeneralLinear.step_val_castSucc_last]
    · rw [pivotColumnEquiv_symm_succAbove, pivotColumnEquiv_symm_succAbove,
        _root_.StableGeneralLinear.step_val_castSucc]
      apply g.property.1
      exact Fin.succAbove_lt_succAbove_iff.mp hji
  · intro i
    rw [permutationGL_conjugate_val]
    exact (upperUnipotent_step F n g).2 _

end Matrix.Bruhat

end

end
