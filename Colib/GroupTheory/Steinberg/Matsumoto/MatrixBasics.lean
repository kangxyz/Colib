/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, kangxyz
-/
module

public import Colib.GroupTheory.Steinberg.Matsumoto.Weyl
public import Colib.GroupTheory.Steinberg.Matsumoto.Torus
public import Colib.GroupTheory.Steinberg.Matsumoto.Normalizer
public import Colib.GroupTheory.Steinberg.Matsumoto.LiftedWeyl
public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary

/-!
# MatrixBasics

Adapted from Quillen Matsumoto/MatrixBasics.lean at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using native matrix units and Milnor coefficients.

The declarations retain their original field, rank, central-kernel and explicit
transport hypotheses. Their current consumer is the finite Matsumoto normalizer,
Bruhat action, or conditional original-root detector construction.
-/

@[expose] public section

/-! ## RootCoordinateDiagonalFaithful -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- The cumulative product through the selected simple-root index. -/
def prefixProduct {n : ℕ} (i : Fin n) : (Fin (n + 1) → Fˣ) →* Fˣ where
  toFun d := ∏ k : Fin (n + 1), if k.val ≤ i.val then d k else 1
  map_one' := by simp
  map_mul' d e := by
    simp only [Pi.mul_apply, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro k _
    split_ifs <;> simp

lemma prefixProduct_single {n : ℕ} (i : Fin n) (k : Fin (n + 1)) (a : Fˣ) :
    prefixProduct F i (Pi.mulSingle k a) = if k.val ≤ i.val then a else 1 := by
  change (∏ j : Fin (n + 1), if j.val ≤ i.val then
    (Pi.mulSingle k a : Fin (n + 1) → Fˣ) j else 1) = _
  rw [Finset.prod_eq_single k]
  · simp
  · intro j _ hjk
    simp [hjk]
  · simp

lemma prefixProduct_simpleDiagonal {n : ℕ} (i j : Fin n) (a : Fˣ) :
    prefixProduct F i (simpleDiagonal F j a) = if j = i then a else 1 := by
  rw [simpleDiagonal, map_mul, prefixProduct_single, prefixProduct_single]
  simp only [Fin.val_castSucc, Fin.val_succ]
  by_cases hji : j = i
  · subst j
    simp
  · have hv : j.val ≠ i.val := by intro h; exact hji (Fin.ext h)
    by_cases hlt : j.val < i.val
    · have hle : j.val ≤ i.val := by omega
      have hs : j.val + 1 ≤ i.val := by omega
      simp [hle, hs, hji]
    · have hle : ¬j.val ≤ i.val := by omega
      have hs : ¬j.val + 1 ≤ i.val := by omega
      simp [hle, hs, hji]

/-- Cumulative products recover every original simple-coroot coordinate. -/
theorem prefixProduct_diagonalCoordinates {n : ℕ} (i : Fin n) (s : Fin n → Fˣ) :
    prefixProduct F i (diagonalCoordinates F s) = s i := by
  rw [diagonalCoordinates, map_prod]
  simp [prefixProduct_simpleDiagonal]

/-- The literal determinant-one coroot diagonal map is injective in every rank. -/
theorem diagonalCoordinates_injective (n : ℕ) :
    Function.Injective (@diagonalCoordinates F _ n) := by
  intro s t he
  funext i
  simpa only [prefixProduct_diagonalCoordinates] using congrArg (prefixProduct F i) he

/-- The actual finite matrix map has exactly the original coefficient kernel. -/
theorem torusToGL_ker (n : ℕ) : (torusToGL F n).ker = (coefficient F n).range := by
  rw [← projection_ker]
  ext x
  constructor
  · intro hx
    change x.diagonal = 1
    apply diagonalCoordinates_injective F n
    rw [diagonalCoordinates_one]
    have hm := congrArg Units.val hx
    change Matrix.diagonal (fun i => (diagonalCoordinates F x.diagonal i : F)) = 1 at hm
    funext i
    apply Units.ext
    have he := congrFun (congrFun hm i) i
    simpa using he
  · intro hx
    apply Units.ext
    change Matrix.diagonal (fun i => (diagonalCoordinates F x.diagonal i : F)) = 1
    change x.diagonal = 1 at hx
    rw [hx, diagonalCoordinates_one]
    simp

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateMatrixAction -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- State permutations inducing literal left matrix multiplication on a supplied state map. -/
def matrixCovariant (n : ℕ)
    (β : NormalizerState F n → Matrix.GeneralLinearGroup (Fin (n + 1)) F)
    (hβ : β (1, 1) = 1) : Subgroup (Equiv.Perm (NormalizerState F n)) where
  carrier := {g | ∀ s, β (g s) = β (g (1, 1)) * β s}
  one_mem' := by intro s; simp only [Equiv.Perm.one_apply, hβ, one_mul]
  mul_mem' := by
    intro g h hg hh s
    change β (g (h s)) = β (g (h (1, 1))) * β s
    rw [hg (h s), hh s, hg (h (1, 1))]
    exact (mul_assoc _ _ _).symm
  inv_mem' := by
    intro g hg
    have hinv (s : NormalizerState F n) : β (g⁻¹ s) = (β (g (1, 1)))⁻¹ * β s := by
      apply (eq_inv_mul_iff_mul_eq).mpr
      have he := hg (g⁻¹ s)
      simpa using he.symm
    intro s
    change β (g⁻¹ s) = β (g⁻¹ (1, 1)) * β s
    rw [hinv s, hinv (1, 1), hβ, mul_one]

/-- Evaluation at the identity state is an actual matrix homomorphism on covariant permutations. -/
def matrixCovariantProjection (n : ℕ)
    (β : NormalizerState F n → Matrix.GeneralLinearGroup (Fin (n + 1)) F)
    (hβ : β (1, 1) = 1) :
    matrixCovariant F n β hβ →* Matrix.GeneralLinearGroup (Fin (n + 1)) F where
  toFun g := β (g.val (1, 1))
  map_one' := hβ
  map_mul' g h := g.property (h.val (1, 1))

/-- A proved state-intertwining equation places the concrete permutation in this subgroup. -/
lemma mem_matrixCovariant_of_intertwining {n : ℕ}
    (β : NormalizerState F n → Matrix.GeneralLinearGroup (Fin (n + 1)) F)
    (hβ : β (1, 1) = 1) (g : Equiv.Perm (NormalizerState F n))
    (A : Matrix.GeneralLinearGroup (Fin (n + 1)) F)
    (hg : ∀ s, β (g s) = A * β s) : g ∈ matrixCovariant F n β hβ := by
  intro s
  rw [hg s, hg (1, 1), hβ, mul_one]

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateMatrixSupport -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- A literal column-monomial identity matrix has the identity permutation. -/
lemma column_support_eq_one {m : ℕ} (A : Matrix (Fin m) (Fin m) F)
    (σ : Equiv.Perm (Fin m)) (c : Fin m → Fˣ)
    (hA : ∀ i j, A i j = if i = σ j then (c j : F) else 0) (h1 : A = 1) : σ = 1 := by
  apply Equiv.ext
  intro j
  change σ j = j
  by_contra hne
  have he := congrFun (congrFun h1 (σ j)) j
  rw [hA] at he
  simp [hne] at he

/-- Literal row and column coefficients differ by composition with the inverse permutation. -/
lemma row_column_diagonal_correction {m : ℕ} (A V : Matrix (Fin m) (Fin m) F)
    (σ : Equiv.Perm (Fin m)) (d c : Fin m → Fˣ)
    (hA : ∀ i j, A i j = if i = σ j then (d i : F) else 0)
    (hV : ∀ i j, V i j = if i = σ j then (c j : F) else 0) :
    Matrix.diagonal (fun i => ((d i * (c (σ.symm i))⁻¹ : Fˣ) : F)) * V = A := by
  ext i j
  rw [Matrix.diagonal_mul, hV, hA]
  by_cases hij : i = σ j
  · subst i
    simp [Units.val_mul]
  · simp [hij]

/-- Multiplication by an actual unit diagonal preserves the literal column permutation. -/
lemma diagonal_mul_column_formula {m : ℕ} (V : Matrix (Fin m) (Fin m) F)
    (σ : Equiv.Perm (Fin m)) (d c : Fin m → Fˣ)
    (hV : ∀ i j, V i j = if i = σ j then (c j : F) else 0) (i j : Fin m) :
    (Matrix.diagonal (fun k => (d k : F)) * V) i j =
      if i = σ j then ((d (σ j) * c j : Fˣ) : F) else 0 := by
  rw [Matrix.diagonal_mul, hV]
  by_cases hij : i = σ j
  · subst i
    simp
  · simp [hij]

end StableSteinberg.RootCoordinate

end

end

/-! ## SimpleWMatrix -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- The literal finite Steinberg Weyl word on adjacent matrix indices. -/
def simpleWMatrix {n : ℕ} (i : Fin n) (a : Fˣ) :
    Matrix.GeneralLinearGroup (Fin (n + 1)) F :=
  Matrix.GeneralLinearGroup.elementary i.castSucc i.succ i.castSucc_lt_succ.ne (a : F) *
    Matrix.GeneralLinearGroup.elementary i.succ i.castSucc i.castSucc_lt_succ.ne.symm
      (-((a⁻¹ : Fˣ) : F)) *
    Matrix.GeneralLinearGroup.elementary i.castSucc i.succ i.castSucc_lt_succ.ne (a : F)

lemma elementary_left_mul_entry {n : ℕ} (g : Matrix.GeneralLinearGroup (Fin n) F)
    (i j : Fin n) (hij : i ≠ j) (a : F) (r s : Fin n) :
    (Matrix.GeneralLinearGroup.elementary i j hij a * g).val r s =
      g.val r s + if r = i then a * g.val j s else 0 := by
  change ((1 + Matrix.single i j a) * g.val) r s = _
  rw [add_mul, one_mul, Matrix.add_apply]
  by_cases hr : r = i
  · subst r
    simp
  · rw [Matrix.single_mul_apply_of_ne a i j r s hr, ite_eq_right hr, add_zero]

/-- The original finite word has its exact two signed rows, in every rank. -/
lemma simpleWMatrix_mul_entry {n : ℕ} (i : Fin n) (a : Fˣ)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) (r s : Fin (n + 1)) :
    (simpleWMatrix F i a * g).val r s =
      if r = i.castSucc then (a : F) * g.val i.succ s else
      if r = i.succ then -((a⁻¹ : Fˣ) : F) * g.val i.castSucc s else g.val r s := by
  have hij : i.castSucc ≠ i.succ := i.castSucc_lt_succ.ne
  simp only [simpleWMatrix, mul_assoc, elementary_left_mul_entry]
  by_cases hri : r = i.castSucc <;> by_cases hrj : r = i.succ <;>
    simp [hri, hrj, hij, hij.symm, Units.val_inv_eq_inv_val]
  all_goals field_simp
  all_goals ring

lemma simpleWMatrix_entry {n : ℕ} (i : Fin n) (a : Fˣ) (r s : Fin (n + 1)) :
    (simpleWMatrix F i a).val r s =
      if r = i.castSucc then (if i.succ = s then (a : F) else 0) else
      if r = i.succ then (if i.castSucc = s then -((a⁻¹ : Fˣ) : F) else 0) else
      if r = s then 1 else 0 := by
  simpa only [mul_one, Units.val_one, Matrix.one_apply, mul_ite, mul_zero] using
    simpleWMatrix_mul_entry F i a 1 r s

/-- The exact existing M1 simple-coroot matrix; no new torus is introduced. -/
lemma torusToGL_simple_entry {n : ℕ} (i : Fin n) (a : Fˣ) (r s : Fin (n + 1)) :
    (torusToGL F n (simple F i a)).val r s =
      if r = s then (simpleDiagonal F i a r : F) else 0 := by
  change (Matrix.diagonal (fun k =>
    (diagonalCoordinates F (Pi.mulSingle i a) k : F))) r s = _
  rw [diagonalCoordinates_single]
  rfl

/-- The original H(a)=W(a)W(-1) word has the actual M1 diagonal value. -/
theorem simpleWMatrix_h {n : ℕ} (i : Fin n) (a : Fˣ) :
    simpleWMatrix F i a * simpleWMatrix F i (-1) = torusToGL F n (simple F i a) := by
  have hij : i.castSucc ≠ i.succ := i.castSucc_lt_succ.ne
  apply Units.ext
  ext r s
  rw [simpleWMatrix_mul_entry, torusToGL_simple_entry]
  simp only [simpleWMatrix_entry]
  by_cases hri : r = i.castSucc <;> by_cases hrj : r = i.succ <;>
    by_cases hsi : s = i.castSucc <;> by_cases hsj : s = i.succ <;>
      simp [hri, hrj, hsi, hsj, hij, hij.symm, simpleDiagonal, eq_comm]

/-- Replacing a by -a is literal inversion of the finite Weyl word. -/
theorem simpleWMatrix_neg {n : ℕ} (i : Fin n) (a : Fˣ) :
    simpleWMatrix F i (-a) = (simpleWMatrix F i a)⁻¹ := by
  have hij : i.castSucc ≠ i.succ := i.castSucc_lt_succ.ne
  have h : simpleWMatrix F i a * simpleWMatrix F i (-a) = 1 := by
    apply Units.ext
    ext r s
    rw [simpleWMatrix_mul_entry]
    simp only [simpleWMatrix_entry]
    by_cases hri : r = i.castSucc <;> by_cases hrj : r = i.succ <;>
      by_cases hsi : s = i.castSucc <;> by_cases hsj : s = i.succ <;>
        simp [hri, hrj, hsi, hsj, hij, hij.symm, Matrix.one_apply, eq_comm]
  have hh := congrArg (fun z : Matrix.GeneralLinearGroup (Fin (n + 1)) F =>
    (simpleWMatrix F i a)⁻¹ * z) h
  simpa only [mul_assoc, inv_mul_cancel_left, mul_one] using hh

lemma simpleWMatrix_neg_one_word {n : ℕ} (i : Fin n) :
    simpleWMatrix F i (-1) =
      Matrix.GeneralLinearGroup.elementary i.castSucc i.succ i.castSucc_lt_succ.ne (-1) *
        Matrix.GeneralLinearGroup.elementary i.succ i.castSucc i.castSucc_lt_succ.ne.symm 1 *
        Matrix.GeneralLinearGroup.elementary i.castSucc i.succ i.castSucc_lt_succ.ne (-1) := by
  simp [simpleWMatrix]

/-- The signed generator used by M2 has square exactly the existing H_i(-1) matrix. -/
theorem simpleWMatrix_neg_one_square {n : ℕ} (i : Fin n) :
    simpleWMatrix F i (-1) * simpleWMatrix F i (-1) =
      torusToGL F n (simple F i (-1)) := simpleWMatrix_h F i (-1)

/-- The opposite generator has the inverse H_i(-1) square before matrix simplification. -/
theorem simpleWMatrix_one_square {n : ℕ} (i : Fin n) :
    simpleWMatrix F i 1 * simpleWMatrix F i 1 =
      (torusToGL F n (simple F i (-1)))⁻¹ := by
  have hm : simpleWMatrix F i 1 = (simpleWMatrix F i (-1))⁻¹ := by
    simpa only [neg_neg] using simpleWMatrix_neg F i (-1)
  have h := congrArg Inv.inv (simpleWMatrix_neg_one_square F i)
  simpa only [_root_.mul_inv_rev, ← hm] using h

end StableSteinberg.RootCoordinate

end

end

/-! ## DiagonalCovariance -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

lemma diagonalCoordinates_castSucc {n : ℕ} (s : Fin n → Fˣ) (i : Fin n) :
    diagonalCoordinates F s i.castSucc = s i * (previous F s i)⁻¹ := by
  have h0 : (∏ j, (Pi.mulSingle j.castSucc (s j) : Fin (n + 1) → Fˣ) i.castSucc) = s i := by
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hji
      simp [hji.symm]
    · simp
  have h1 : (∏ j, (Pi.mulSingle j.succ ((s j)⁻¹) : Fin (n + 1) → Fˣ) i.castSucc) =
      (previous F s i)⁻¹ := by
    unfold previous
    split_ifs with h
    · let j : Fin n := ⟨i.val - 1, by omega⟩
      have hj : j.succ = i.castSucc := by apply Fin.ext; dsimp [j]; omega
      rw [Finset.prod_eq_single j]
      · simp [hj, j]
      · intro k _ hkj
        have hk : k.succ ≠ i.castSucc := by
          intro he
          have hv := congrArg Fin.val he
          apply hkj
          apply Fin.ext
          dsimp [j]
          simp only [Fin.val_succ, Fin.val_castSucc] at hv
          omega
        simp [hk.symm]
      · simp
    · have hk (k : Fin n) : k.succ ≠ i.castSucc := by
        intro he
        have hv := congrArg Fin.val he
        simp only [Fin.val_succ, Fin.val_castSucc] at hv
        omega
      simp [fun k => (hk k).symm]
  simp only [diagonalCoordinates, Finset.prod_apply, simpleDiagonal, Pi.mul_apply]
  rw [Finset.prod_mul_distrib, h0, h1]

lemma diagonalCoordinates_succ {n : ℕ} (s : Fin n → Fˣ) (i : Fin n) :
    diagonalCoordinates F s i.succ = following F s i * (s i)⁻¹ := by
  have h0 : (∏ j, (Pi.mulSingle j.castSucc (s j) : Fin (n + 1) → Fˣ) i.succ) =
      following F s i := by
    unfold following
    split_ifs with h
    · let j : Fin n := ⟨i.val + 1, h⟩
      have hj : j.castSucc = i.succ := Fin.ext rfl
      rw [Finset.prod_eq_single j]
      · simp [hj, j]
      · intro k _ hkj
        have hk : k.castSucc ≠ i.succ := by
          intro he
          have hv := congrArg Fin.val he
          exact hkj (Fin.ext hv)
        simp [hk.symm]
      · simp
    · have hk (k : Fin n) : k.castSucc ≠ i.succ := by
        intro he
        have hv := congrArg Fin.val he
        simp only [Fin.val_castSucc, Fin.val_succ] at hv
        omega
      simp [fun k => (hk k).symm]
  have h1 : (∏ j, (Pi.mulSingle j.succ ((s j)⁻¹) : Fin (n + 1) → Fˣ) i.succ) =
      (s i)⁻¹ := by
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hji
      simp [hji.symm]
    · simp
  simp only [diagonalCoordinates, Finset.prod_apply, simpleDiagonal, Pi.mul_apply]
  rw [Finset.prod_mul_distrib, h0, h1]

/-- The existing root-coordinate reflection swaps exactly two actual diagonal entries. -/
theorem diagonalCoordinates_reflect_swap {n : ℕ} (i : Fin n) (s : Fin n → Fˣ) :
    diagonalCoordinates F (reflectionCoordinates F i s) =
      fun r => diagonalCoordinates F s (Equiv.swap i.castSucc i.succ r) := by
  unfold reflectionCoordinates
  rw [diagonalCoordinates_mul, diagonalCoordinates_single]
  funext r
  change diagonalCoordinates F s r * simpleDiagonal F i (reflectionDelta F i s) r = _
  have hij : i.castSucc ≠ i.succ := i.castSucc_lt_succ.ne
  by_cases hri : r = i.castSucc
  · subst r
    simp [simpleDiagonal, reflectionDelta, diagonalCoordinates_castSucc,
      diagonalCoordinates_succ, hij, mul_assoc, mul_comm, mul_left_comm]
  · by_cases hrj : r = i.succ
    · subst r
      simp [simpleDiagonal, reflectionDelta, diagonalCoordinates_castSucc,
        diagonalCoordinates_succ, hij.symm, mul_assoc, mul_comm, mul_left_comm]
    · simp [simpleDiagonal, hri, hrj, Equiv.swap_apply_def]

lemma torusToGL_entry {n : ℕ} (h : Torus F n) (r s : Fin (n + 1)) :
    (torusToGL F n h).val r s =
      if r = s then (diagonalCoordinates F h.diagonal r : F) else 0 := rfl

/-- Covariance of the actual M1 torus map, proved in the original finite GL units. -/
theorem torusToGL_reflection_covariance {n : ℕ} (i : Fin n) (a : Fˣ) (h : Torus F n) :
    torusToGL F n (reflection F i h) =
      simpleWMatrix F i a * torusToGL F n h * (simpleWMatrix F i a)⁻¹ := by
  have hij : i.castSucc ≠ i.succ := i.castSucc_lt_succ.ne
  have hinter : torusToGL F n (reflection F i h) * simpleWMatrix F i a =
      simpleWMatrix F i a * torusToGL F n h := by
    apply Units.ext
    ext r s
    change (Matrix.diagonal (fun k =>
        (diagonalCoordinates F (reflectionCoordinates F i h.diagonal) k : F)) *
        (simpleWMatrix F i a).val) r s = (simpleWMatrix F i a * torusToGL F n h).val r s
    rw [Matrix.diagonal_mul, simpleWMatrix_mul_entry, diagonalCoordinates_reflect_swap]
    simp only [simpleWMatrix_entry, torusToGL_entry]
    by_cases hri : r = i.castSucc <;> by_cases hrj : r = i.succ <;>
      simp [hri, hrj, hij.symm, Equiv.swap_apply_def, eq_comm, mul_comm,
        mul_ite, ite_mul]
  have he := congrArg (fun z : Matrix.GeneralLinearGroup (Fin (n + 1)) F =>
    z * (simpleWMatrix F i a)⁻¹) hinter
  simpa only [mul_assoc, mul_inv_cancel, mul_one] using he

/-- Theta is the inverse frozen reflection and is represented by the literal W_i(-1). -/
theorem torusToGL_theta_covariance {n : ℕ} (i : Fin n) (h : Torus F n) :
    torusToGL F n ((reflection F i).symm h) =
      simpleWMatrix F i (-1) * torusToGL F n h * (simpleWMatrix F i (-1))⁻¹ := by
  have he : torusToGL F n ((reflection F i).symm h) = torusToGL F n (reflection F i h) := by
    apply Units.ext
    rfl
  rw [he]
  exact torusToGL_reflection_covariance F i (-1) h

end StableSteinberg.RootCoordinate

end

end

/-! ## SimpleWRelations -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- Literal distant Weyl matrices commute, retaining arbitrary unit parameters. -/
theorem simpleWMatrix_distant {n : ℕ} (i j : Fin n) (hne : i ≠ j)
    (hij : i.val + 1 ≠ j.val) (hji : j.val + 1 ≠ i.val) (a b : Fˣ) :
    simpleWMatrix F i a * simpleWMatrix F j b =
      simpleWMatrix F j b * simpleWMatrix F i a := by
  have h00 : i.castSucc ≠ j.castSucc := by simpa using hne
  have h11 : i.succ ≠ j.succ := by simpa using hne
  have h01 : i.castSucc ≠ j.succ := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at hv
    exact hji hv.symm
  have h10 : i.succ ≠ j.castSucc := by
    intro h
    exact hij (congrArg Fin.val h)
  apply Units.ext
  ext r s
  simp only [simpleWMatrix_mul_entry, simpleWMatrix_entry]
  by_cases hri0 : r = i.castSucc <;> by_cases hri1 : r = i.succ <;>
    by_cases hrj0 : r = j.castSucc <;> by_cases hrj1 : r = j.succ <;>
      simp_all [eq_comm]

/-- The literal adjacent signed Weyl matrices satisfy the type-A braid. -/
theorem simpleWMatrix_braid_forward {n : ℕ} (i j : Fin n) (hij : i.val + 1 = j.val) :
    simpleWMatrix F i (-1) * simpleWMatrix F j (-1) * simpleWMatrix F i (-1) =
      simpleWMatrix F j (-1) * simpleWMatrix F i (-1) * simpleWMatrix F j (-1) := by
  have hj : j.castSucc ≠ j.succ := j.castSucc_lt_succ.ne
  have hne : i ≠ j := by intro h; have := congrArg Fin.val h; omega
  have h00 : i.castSucc ≠ j.castSucc := by simpa using hne
  have h10 : i.succ = j.castSucc := Fin.ext hij
  have h01 : i.castSucc ≠ j.succ := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at hv
    omega
  simp only [mul_assoc]
  apply Units.ext
  ext r s
  simp only [simpleWMatrix_mul_entry, simpleWMatrix_entry]
  by_cases hri0 : r = i.castSucc
  · subst r
    simp [hj, h00, h10, h01, eq_comm]
  · by_cases hri1 : r = i.succ
    · subst r
      simp [hj, h00, h10, h01, eq_comm]
    · by_cases hrj1 : r = j.succ
      · subst r
        simp [hj, h00, h10, h01, eq_comm]
      · have hrj0 : r ≠ j.castSucc := by simpa only [← h10] using hri1
        simp [hri0, hri1, hrj0, hrj1]

theorem simpleWMatrix_braid {n : ℕ} (i j : Fin n)
    (hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val) :
    simpleWMatrix F i (-1) * simpleWMatrix F j (-1) * simpleWMatrix F i (-1) =
      simpleWMatrix F j (-1) * simpleWMatrix F i (-1) * simpleWMatrix F j (-1) := by
  rcases hadj with h | h
  · exact simpleWMatrix_braid_forward F i j h
  · exact (simpleWMatrix_braid_forward F j i h).symm

end StableSteinberg.RootCoordinate

end

end
