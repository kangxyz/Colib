/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, kangxyz
-/
module

public import Colib.GroupTheory.Steinberg.Matsumoto.MatrixBasics
public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.SignedSection
public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary
public import Colib.GroupTheory.Steinberg.Matsumoto.LiftedWeyl
public import Colib.GroupTheory.Steinberg.Matsumoto.Torus
public import Colib.GroupTheory.Steinberg.Matsumoto.Weyl
public import Colib.GroupTheory.Steinberg.Matsumoto.Normalizer
public import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# NormalizerMatrix

Adapted from Quillen Algebra/Group/StableSteinberg/Matsumoto/NormalizerMatrix.lean at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using native matrix units and Milnor coefficients.

The declarations retain their original field, rank, central-kernel and explicit
transport hypotheses. Their current consumer is the finite Matsumoto normalizer,
Bruhat action, or conditional original-root detector construction.
-/

@[expose] public section

/-! ## RootCoordinateSectionBridge -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- The two independently written finite Weyl words are literally the same elementary product. -/
lemma sectionWminus_eq {n : ℕ} (i : Fin n) :
    _root_.Matrix.GeneralLinearGroup.SignedSection.Wminus F i = simpleWMatrix F i (-1) :=
  (simpleWMatrix_neg_one_word F i).symm

/-- The section recurrence's signed diagonal is the actual image of H_i(-1). -/
lemma torus_simple_neg_one_eq_sectionE {n : ℕ} (i : Fin n) :
    torusToGL F n (simple F i (-1)) = _root_.Matrix.GeneralLinearGroup.SignedSection.E F i := by
  have hne : i.castSucc ≠ i.succ := i.castSucc_lt_succ.ne
  apply Units.ext
  ext r s
  rw [torusToGL_simple_entry, _root_.Matrix.GeneralLinearGroup.SignedSection.E_entry]
  by_cases hrs : r = s
  · subst s
    by_cases hra : r = i.castSucc
    · subst r
      simp [simpleDiagonal, hne]
    · by_cases hrb : r = i.succ
      · subst r
        simp [simpleDiagonal, hne.symm]
      · simp [simpleDiagonal, hra, hrb]
  · simp [hrs]

/-- The actual matrix of a torus-permutation state, with its literal column section. -/
def stateMatrix {n : ℕ} (s : NormalizerState F n) :
    Matrix.GeneralLinearGroup (Fin (n + 1)) F :=
  torusToGL F n s.1 * _root_.Matrix.GeneralLinearGroup.SignedSection.sectionGL F s.2

@[simp] lemma stateMatrix_one (n : ℕ) : stateMatrix F ((1, 1) : NormalizerState F n) = 1 := by
  simp [stateMatrix]

lemma stateMatrix_torusLeft {n : ℕ} (h : Torus F n) (s : NormalizerState F n) :
    stateMatrix F (torusLeft F n h s) = torusToGL F n h * stateMatrix F s := by
  change torusToGL F n (h * s.1) * _root_.Matrix.GeneralLinearGroup.SignedSection.sectionGL F s.2 =
    _
  rw [map_mul, mul_assoc]
  rfl

/-- The actual lifted W_i(-1) permutation intertwines the literal finite Weyl matrix. -/
theorem stateMatrix_liftedWeyl {n : ℕ} (i : Fin n) (s : NormalizerState F n) :
    stateMatrix F (liftedWeyl F i s) = simpleWMatrix F i (-1) * stateMatrix F s := by
  classical
  change torusToGL F n (theta F i (s.1 * descentCarry F i s.2)) *
      _root_.Matrix.GeneralLinearGroup.SignedSection.sectionGL F (simpleSwap i * s.2) =
    simpleWMatrix F i (-1) * (torusToGL F n s.1 *
      _root_.Matrix.GeneralLinearGroup.SignedSection.sectionGL F s.2)
  by_cases hp : isAscent i s.2
  · simp only [descentCarry, hp, ↓reduceIte, mul_one]
    rw [theta, torusToGL_theta_covariance, ← sectionWminus_eq]
    change _ * _root_.Matrix.GeneralLinearGroup.SignedSection.sectionGL F
      (_root_.Matrix.GeneralLinearGroup.SignedSection.adjacentSwap i * s.2) = _
    rw [← _root_.Matrix.GeneralLinearGroup.SignedSection.Wminus_section_ascent F s.2 i hp]
    group
  · have hne : s.2.symm i.castSucc ≠ s.2.symm i.succ :=
      s.2.symm.injective.ne i.castSucc_lt_succ.ne
    have hd : s.2.symm i.succ < s.2.symm i.castSucc :=
      lt_of_le_of_ne (le_of_not_gt hp) hne.symm
    simp only [descentCarry, hp, ↓reduceIte, map_mul, theta_simple_neg_one]
    rw [theta, torusToGL_theta_covariance, torus_simple_neg_one_eq_sectionE,
      ← sectionWminus_eq]
    change (_ * _root_.Matrix.GeneralLinearGroup.SignedSection.E F i) *
      _root_.Matrix.GeneralLinearGroup.SignedSection.sectionGL F
        (_root_.Matrix.GeneralLinearGroup.SignedSection.adjacentSwap i * s.2) = _
    rw [mul_assoc, ← _root_.Matrix.GeneralLinearGroup.SignedSection.Wminus_section_descent F s.2 i
      hd]
    group

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateNormalizerMatrix -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

lemma normalizer_le_matrixCovariant (n : ℕ) :
    LiftedNormalizer F n ≤ matrixCovariant F n (stateMatrix F) (stateMatrix_one F n) := by
  apply (Subgroup.closure_le _).mpr
  rintro g (⟨h, rfl⟩ | ⟨i, rfl⟩)
  · exact mem_matrixCovariant_of_intertwining F (stateMatrix F) (stateMatrix_one F n)
      (torusLeft F n h) (torusToGL F n h) (stateMatrix_torusLeft F h)
  · exact mem_matrixCovariant_of_intertwining F (stateMatrix F) (stateMatrix_one F n)
      (liftedWeyl F i) (simpleWMatrix F i (-1)) (stateMatrix_liftedWeyl F i)

/-- The actual finite matrix projection of the concrete lifted normalizer. -/
def normalizerToGL (n : ℕ) : LiftedNormalizer F n →*
    Matrix.GeneralLinearGroup (Fin (n + 1)) F :=
  (matrixCovariantProjection F n (stateMatrix F) (stateMatrix_one F n)).comp
    (Subgroup.inclusion (normalizer_le_matrixCovariant F n))

lemma normalizerToGL_apply (n : ℕ) (g : LiftedNormalizer F n) :
    normalizerToGL F n g = stateMatrix F (normalizerEvaluation F n g) := rfl

@[simp] lemma normalizerToGL_torus (n : ℕ) (h : Torus F n) :
    normalizerToGL F n (normalizerTorus F n h) = torusToGL F n h := by
  change torusToGL F n (h * 1) * _root_.Matrix.GeneralLinearGroup.SignedSection.sectionGL F 1 =
    torusToGL F n h
  simp

@[simp] lemma normalizerToGL_lambda {n : ℕ} (i : Fin n) :
    normalizerToGL F n (normalizerLambda F i) = simpleWMatrix F i (-1) := by
  change stateMatrix F (liftedWeyl F i (1, 1)) = simpleWMatrix F i (-1)
  rw [stateMatrix_liftedWeyl, stateMatrix_one, mul_one]

/-- The normalized W element projects to the original elementary-matrix Weyl word. -/
theorem normalizerToGL_W {n : ℕ} (i : Fin n) (a : Fˣ) :
    normalizerToGL F n (normalizerW F i a) = simpleWMatrix F i a := by
  rw [normalizerW, map_mul, map_inv, normalizerToGL_torus, normalizerToGL_lambda,
    ← simpleWMatrix_h]
  simp [mul_assoc]

@[simp] lemma normalizerToGL_coefficient (n : ℕ) (a : Multiplicative (MilnorKTheory F 2)) :
    normalizerToGL F n (normalizerCoefficient F n a) = 1 := by
  change normalizerToGL F n (normalizerTorus F n (coefficient F n a)) = 1
  rw [normalizerToGL_torus]
  change coefficient F n a ∈ (torusToGL F n).ker
  rw [torusToGL_ker]
  exact ⟨a, rfl⟩

/-- The state map has the literal column permutation, after the row-diagonal correction. -/
lemma stateMatrix_entry {n : ℕ} (s : NormalizerState F n) (r j : Fin (n + 1)) :
    (stateMatrix F s).val r j = if r = s.2 j then
      ((diagonalCoordinates F s.1.diagonal (s.2 j) *
        (-1 : Fˣ) ^ _root_.Matrix.GeneralLinearGroup.SignedSection.prefixCount s.2 j : Fˣ) : F) else
          0 := by
  change (Matrix.diagonal (fun k => (diagonalCoordinates F s.1.diagonal k : F)) *
    (_root_.Matrix.GeneralLinearGroup.SignedSection.sectionGL F s.2).val) r j = _
  exact diagonal_mul_column_formula F (_root_.Matrix.GeneralLinearGroup.SignedSection.sectionGL F
    s.2).val s.2
    (diagonalCoordinates F s.1.diagonal)
    (fun j => (-1 : Fˣ) ^ _root_.Matrix.GeneralLinearGroup.SignedSection.prefixCount s.2 j) (fun _ _
      => rfl) r j

/-- The actual GL kernel is precisely the unchanged, faithfully embedded Milnor coefficient. -/
theorem normalizerToGL_ker (n : ℕ) :
    (normalizerToGL F n).ker = (normalizerCoefficient F n).range := by
  apply le_antisymm
  · intro g hg
    have hp : normalizerPermutation F n g = 1 := by
      change (normalizerEvaluation F n g).2 = 1
      apply column_support_eq_one F (normalizerToGL F n g).val
        (normalizerEvaluation F n g).2
        (fun j => diagonalCoordinates F (normalizerEvaluation F n g).1.diagonal
          ((normalizerEvaluation F n g).2 j) *
            (-1 : Fˣ) ^ _root_.Matrix.GeneralLinearGroup.SignedSection.prefixCount
              (normalizerEvaluation F n g).2 j)
      · exact stateMatrix_entry F (normalizerEvaluation F n g)
      · exact congrArg Units.val hg
    have ht : g ∈ (normalizerTorus F n).range := by
      rw [← normalizerPermutation_ker]
      exact hp
    obtain ⟨h, rfl⟩ := ht
    change normalizerToGL F n (normalizerTorus F n h) = 1 at hg
    rw [normalizerToGL_torus] at hg
    have hh : h ∈ (coefficient F n).range := by
      rw [← torusToGL_ker]
      exact hg
    obtain ⟨a, rfl⟩ := hh
    exact ⟨a, rfl⟩
  · rintro _ ⟨a, rfl⟩
    exact normalizerToGL_coefficient F n a

/-- Centrality for the actual finite matrix projection, with no onto-GL assertion. -/
theorem normalizerToGL_ker_central (n : ℕ) :
    (normalizerToGL F n).ker ≤ Subgroup.center (LiftedNormalizer F n) := by
  rw [normalizerToGL_ker]
  exact normalizerCoefficient_le_center F n

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateNormalizerDeterminant -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

lemma elementaryUnit_det {m : ℕ} (i j : Fin m) (hij : i ≠ j) (a : F) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.elementary i j hij a) = 1 := by
  apply Units.ext
  exact Matrix.det_transvection_of_ne i j hij a

lemma simpleWMatrix_det {n : ℕ} (i : Fin n) (a : Fˣ) :
    Matrix.GeneralLinearGroup.det (simpleWMatrix F i a) = 1 := by
  simp only [simpleWMatrix, map_mul, elementaryUnit_det, one_mul]

/-- Every actual normalizer matrix has determinant one, proved on the genuine generators. -/
theorem normalizerToGL_det (n : ℕ) (g : LiftedNormalizer F n) :
    Matrix.GeneralLinearGroup.det (normalizerToGL F n g) = 1 := by
  let d : LiftedNormalizer F n →* Fˣ :=
    Matrix.GeneralLinearGroup.det.comp (normalizerToGL F n)
  have htop : d.ker = ⊤ := by
    apply normalizer_generated F n
    · intro h
      change Matrix.GeneralLinearGroup.det (normalizerToGL F n (normalizerTorus F n h)) = 1
      rw [normalizerToGL_torus]
      apply Units.ext
      exact torusToGL_det F n h
    · intro i
      change Matrix.GeneralLinearGroup.det (normalizerToGL F n (normalizerLambda F i)) = 1
      rw [normalizerToGL_lambda, simpleWMatrix_det]
  have hg : g ∈ d.ker := by rw [htop]; trivial
  exact hg

/-- The section has determinant one as a consequence of the constructed regular action. -/
theorem signedSection_det (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    Matrix.GeneralLinearGroup.det (_root_.Matrix.GeneralLinearGroup.SignedSection.sectionGL F σ) = 1
      := by
  let g := (normalizerStateEquiv F n).symm (1, σ)
  have he : normalizerEvaluation F n g = (1, σ) :=
    (normalizerStateEquiv F n).apply_symm_apply (1, σ)
  have hd := normalizerToGL_det F n g
  rw [normalizerToGL_apply, he] at hd
  simpa only [stateMatrix, map_one, one_mul] using hd

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateDiagonalOnto -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- Inclusive cumulative products of a literal finite diagonal tuple. -/
def cumulativeDiagonal {n : ℕ} (d : Fin n → Fˣ) (i : Fin n) : Fˣ :=
  ∏ k : Fin n, if k.val ≤ i.val then d k else 1

lemma cumulativeDiagonal_zero {n : ℕ} (d : Fin (n + 1) → Fˣ) :
    cumulativeDiagonal F d 0 = d 0 := by
  unfold cumulativeDiagonal
  rw [Finset.prod_eq_single 0]
  · simp
  · intro k _ hk
    have hle : ¬k.val ≤ 0 := by
      intro h
      apply hk
      apply Fin.ext
      simp only [Fin.val_zero]
      omega
    simp [hle]
  · simp

lemma cumulativeDiagonal_succ {n : ℕ} (d : Fin (n + 1) → Fˣ) (i : Fin n) :
    cumulativeDiagonal F d i.succ = cumulativeDiagonal F d i.castSucc * d i.succ := by
  calc
    _ = ∏ k : Fin (n + 1), (if k.val ≤ i.val then d k else 1) *
        (Pi.mulSingle i.succ (d i.succ) : Fin (n + 1) → Fˣ) k := by
      unfold cumulativeDiagonal
      apply Finset.prod_congr rfl
      intro k _
      by_cases hki : k = i.succ
      · subst k
        simp
      · have hv : k.val ≠ i.val + 1 := by
          intro h
          exact hki (Fin.ext h)
        by_cases hk : k.val ≤ i.val
        · have hk' : k.val ≤ i.val + 1 := by omega
          simp [hk, hk', hki]
        · have hk' : ¬k.val ≤ i.val + 1 := by omega
          simp [hk, hk', hki]
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      simp [cumulativeDiagonal]

lemma cumulativeDiagonal_last {n : ℕ} (d : Fin (n + 1) → Fˣ) :
    cumulativeDiagonal F d (Fin.last n) = ∏ i, d i := by
  have hle (i : Fin (n + 1)) : i.val ≤ n := by omega
  simp [cumulativeDiagonal, hle]

lemma cumulativeDiagonal_injective (n : ℕ) :
    Function.Injective (@cumulativeDiagonal F _ n) := by
  intro d e he
  cases n with
  | zero => exact Subsingleton.elim _ _
  | succ n =>
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simpa only [cumulativeDiagonal_zero] using congrFun he 0
    · have hs := congrFun he i.succ
      have hp := congrFun he i.castSucc
      rw [cumulativeDiagonal_succ, cumulativeDiagonal_succ, hp] at hs
      exact mul_left_cancel hs

/-- The actual simple-coroot parameters recovered from a determinant-one diagonal. -/
def corootsOfDiagonal {n : ℕ} (d : Fin (n + 1) → Fˣ) : Fin n → Fˣ :=
  fun i => prefixProduct F i d

/-- Every literal determinant-one diagonal has its explicit simple-coroot factorization. -/
theorem diagonalCoordinates_corootsOfDiagonal {n : ℕ} (d : Fin (n + 1) → Fˣ)
    (hd : ∏ i, d i = 1) : diagonalCoordinates F (corootsOfDiagonal F d) = d := by
  apply cumulativeDiagonal_injective F (n + 1)
  funext k
  refine Fin.lastCases ?_ (fun i => ?_) k
  · rw [cumulativeDiagonal_last, diagonalCoordinates_prod, cumulativeDiagonal_last, hd]
  · change prefixProduct F i (diagonalCoordinates F (corootsOfDiagonal F d)) =
      prefixProduct F i d
    rw [prefixProduct_diagonalCoordinates]
    rfl

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateNormalizerOnto -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- Every actual determinant-one row-monomial matrix has a lift in the constructed normalizer. -/
theorem normalizerToGL_row_preimage {n : ℕ}
    (A : Matrix.GeneralLinearGroup (Fin (n + 1)) F)
    (σ : Equiv.Perm (Fin (n + 1))) (d : Fin (n + 1) → Fˣ)
    (hA : ∀ r j, A.val r j = if r = σ j then (d r : F) else 0)
    (hdet : Matrix.GeneralLinearGroup.det A = 1) :
    ∃ g : LiftedNormalizer F n, normalizerToGL F n g = A := by
  let c : Fin (n + 1) → Fˣ := fun j => (-1 : Fˣ) ^
    _root_.Matrix.GeneralLinearGroup.SignedSection.prefixCount σ j
  let e : Fin (n + 1) → Fˣ := fun r => d r * (c (σ.symm r))⁻¹
  have hdiag : Matrix.diagonal (fun r => (e r : F)) *
    (_root_.Matrix.GeneralLinearGroup.SignedSection.sectionGL F σ).val =
      A.val := row_column_diagonal_correction F A.val
        (_root_.Matrix.GeneralLinearGroup.SignedSection.sectionGL F σ).val
        σ d c hA (fun _ _ => rfl)
  have he : ∏ r, e r = 1 := by
    have hd := congrArg Matrix.det hdiag
    have hv : Matrix.det (_root_.Matrix.GeneralLinearGroup.SignedSection.sectionGL F σ).val = 1 :=
      congrArg Units.val (signedSection_det F n σ)
    have ha : Matrix.det A.val = 1 := congrArg Units.val hdet
    rw [Matrix.det_mul, Matrix.det_diagonal, hv, mul_one, ha] at hd
    apply Units.ext
    simpa only [Units.coe_prod, Units.val_one] using hd
  let t : Torus F n := torusLift F n (corootsOfDiagonal F e)
  have ht : (torusToGL F n t).val = Matrix.diagonal (fun r => (e r : F)) := by
    change Matrix.diagonal (fun r =>
      (diagonalCoordinates F (corootsOfDiagonal F e) r : F)) = _
    rw [diagonalCoordinates_corootsOfDiagonal F e he]
  let g := (normalizerStateEquiv F n).symm (t, σ)
  refine ⟨g, ?_⟩
  have hg : normalizerEvaluation F n g = (t, σ) :=
    (normalizerStateEquiv F n).apply_symm_apply (t, σ)
  rw [normalizerToGL_apply, hg]
  apply Units.ext
  change (torusToGL F n t).val * (_root_.Matrix.GeneralLinearGroup.SignedSection.sectionGL F σ).val
    = A.val
  rw [ht]
  exact hdiag

/-- Column monomials lift after the explicit inverse-permutation coefficient change. -/
theorem normalizerToGL_column_preimage {n : ℕ}
    (A : Matrix.GeneralLinearGroup (Fin (n + 1)) F)
    (σ : Equiv.Perm (Fin (n + 1))) (c : Fin (n + 1) → Fˣ)
    (hA : ∀ r j, A.val r j = if r = σ j then (c j : F) else 0)
    (hdet : Matrix.GeneralLinearGroup.det A = 1) :
    ∃ g : LiftedNormalizer F n, normalizerToGL F n g = A := by
  apply normalizerToGL_row_preimage F A σ (fun r => c (σ.symm r)) ?_ hdet
  intro r j
  rw [hA]
  by_cases hrj : r = σ j
  · subst r
    simp
  · simp [hrj]

/-- The actual range is exactly the determinant-one monomial matrices, in literal entries. -/
theorem normalizerToGL_mem_range_iff (n : ℕ)
    (A : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    A ∈ (normalizerToGL F n).range ↔ Matrix.GeneralLinearGroup.det A = 1 ∧
      ∃ (σ : Equiv.Perm (Fin (n + 1))) (c : Fin (n + 1) → Fˣ),
        ∀ r j, A.val r j = if r = σ j then (c j : F) else 0 := by
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨normalizerToGL_det F n g, (normalizerEvaluation F n g).2, ?_⟩
    refine ⟨fun j => diagonalCoordinates F (normalizerEvaluation F n g).1.diagonal
      ((normalizerEvaluation F n g).2 j) *
        (-1 : Fˣ) ^ _root_.Matrix.GeneralLinearGroup.SignedSection.prefixCount (normalizerEvaluation
          F n g).2 j, ?_⟩
    exact stateMatrix_entry F (normalizerEvaluation F n g)
  · rintro ⟨hd, σ, c, hA⟩
    exact normalizerToGL_column_preimage F A σ c hA hd

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCoordinateNormalizerSign -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- The fourth power retains the original central {-1,-1} coefficient. -/
theorem normalizerW_neg_one_pow_four {n : ℕ} (i : Fin n) :
    normalizerW F i (-1) ^ 4 =
      normalizerCoefficient F n (Multiplicative.ofAdd (milnorKTupleSymbol ![-1, -1])) := by
  calc
    _ = (normalizerLambda F i * normalizerLambda F i) *
        (normalizerLambda F i * normalizerLambda F i) := by
      rw [normalizerW_neg_one]
      simp [pow_succ, mul_assoc]
    _ = normalizerTorus F n (simple F i (-1)) *
        normalizerTorus F n (simple F i (-1)) := by rw [normalizerLambda_square]
    _ = normalizerTorus F n (simple F i (-1) * simple F i (-1)) := (map_mul _ _ _).symm
    _ = _ := by rw [simple_neg_one_square]; rfl

/-- Faithfulness makes vanishing of that fourth power equivalent to actual symbol vanishing. -/
theorem normalizerW_neg_one_pow_four_eq_one_iff {n : ℕ} (i : Fin n) :
    normalizerW F i (-1) ^ 4 = 1 ↔ (milnorKTupleSymbol ![-1, -1] : MilnorKTheory F 2) = 0 := by
  rw [normalizerW_neg_one_pow_four]
  constructor
  · intro he
    have ha : (Multiplicative.ofAdd (milnorKTupleSymbol ![-1, -1]) :
        Multiplicative (MilnorKTheory F 2)) = 1 := by
      apply normalizerCoefficient_injective F n
      rw [map_one]
      exact he
    exact congrArg Multiplicative.toAdd ha
  · intro he
    rw [he]
    exact map_one _

end StableSteinberg.RootCoordinate

end

end
