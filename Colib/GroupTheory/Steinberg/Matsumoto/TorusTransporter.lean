/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, kangxyz
-/
module

public import Colib.GroupTheory.Steinberg.Matsumoto.NormalizerMatrix
public import Colib.GroupTheory.Steinberg.Matsumoto.Normalizer
public import Colib.GroupTheory.Steinberg.Matsumoto.Weyl
public import Colib.GroupTheory.Steinberg.Matsumoto.Torus
public import Colib.GroupTheory.Steinberg.Matsumoto.MatrixBasics
public import Colib.GroupTheory.Steinberg.Matsumoto.LiftedWeyl
public import Colib.LinearAlgebra.Matrix.Bruhat.Coordinates
public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.SignedSection

/-!
# TorusTransporter

Adapted from Quillen Matsumoto/TorusTransporter.lean at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using the native Stacks
homogeneous Milnor group and native matrix units throughout.

The declarations retain their original field, rank, central-kernel and explicit
transport hypotheses. Their current consumer is the finite Matsumoto normalizer,
Bruhat action, or conditional original-root detector construction.
-/

@[expose] public section

/-! ## RootCorootCoordinates -/

section

open scoped BigOperators

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- The literal determinant-one diagonal for an ordered pair of finite positions. -/
def rootDiagonal {n : ℕ} (p q : Fin (n + 1)) (t : Fˣ) : Fin (n + 1) → Fˣ :=
  Pi.mulSingle p t * Pi.mulSingle q t⁻¹

lemma rootDiagonal_prod {n : ℕ} (p q : Fin (n + 1)) (t : Fˣ) :
    ∏ r, rootDiagonal F p q t r = 1 := by
  simp [rootDiagonal, Finset.prod_mul_distrib]

/-- The actual simple-coroot coordinates of this ordered root diagonal. -/
def rootCoordinates {n : ℕ} (p q : Fin (n + 1)) (t : Fˣ) : Fin n → Fˣ :=
  corootsOfDiagonal F (rootDiagonal F p q t)

lemma rootCoordinates_apply {n : ℕ} (p q : Fin (n + 1)) (t : Fˣ) (r : Fin n) :
    rootCoordinates F p q t r =
      (if p.val ≤ r.val then t else 1) * (if q.val ≤ r.val then t⁻¹ else 1) := by
  change prefixProduct F r (Pi.mulSingle p t * Pi.mulSingle q t⁻¹) = _
  rw [map_mul, prefixProduct_single, prefixProduct_single]

lemma diagonalCoordinates_rootCoordinates {n : ℕ} (p q : Fin (n + 1)) (t : Fˣ) :
    diagonalCoordinates F (rootCoordinates F p q t) = rootDiagonal F p q t :=
  diagonalCoordinates_corootsOfDiagonal F _ (rootDiagonal_prod F p q t)

lemma previous_rootCoordinates {n : ℕ} (p q : Fin (n + 1)) (t : Fˣ) (i : Fin n) :
    previous F (rootCoordinates F p q t) i =
      (if p.val < i.val then t else 1) * (if q.val < i.val then t⁻¹ else 1) := by
  unfold previous
  by_cases h : 0 < i.val
  · simp only [h, dite_true]
    rw [rootCoordinates_apply]
    have hp : p.val ≤ i.val - 1 ↔ p.val < i.val := by omega
    have hq : q.val ≤ i.val - 1 ↔ q.val < i.val := by omega
    simp only [hp, hq]
  · simp only [h, dite_false]
    have hp : ¬p.val < i.val := by omega
    have hq : ¬q.val < i.val := by omega
    simp [hp, hq]

lemma following_rootCoordinates {n : ℕ} (p q : Fin (n + 1)) (t : Fˣ) (i : Fin n) :
    following F (rootCoordinates F p q t) i =
      (if p.val ≤ i.val + 1 then t else 1) * (if q.val ≤ i.val + 1 then t⁻¹ else 1) := by
  unfold following
  by_cases h : i.val + 1 < n
  · simp only [h, dite_true]
    rw [rootCoordinates_apply]
  · simp only [h, dite_false]
    have hp : p.val ≤ i.val + 1 := by omega
    have hq : q.val ≤ i.val + 1 := by omega
    simp [hp, hq]

lemma rootCoordinates_simple {n : ℕ} (i : Fin n) (t : Fˣ) :
    rootCoordinates F i.castSucc i.succ t = Pi.mulSingle i t := by
  funext r
  rw [rootCoordinates_apply]
  by_cases hr : r = i
  · subst r
    simp
  · have hri : r.val ≠ i.val := by intro he; exact hr (Fin.ext he)
    by_cases hi : i.val < r.val
    · have hle : i.val ≤ r.val := by omega
      have hs : i.val + 1 ≤ r.val := by omega
      simp [hle, hs, hr]
    · have hle : ¬i.val ≤ r.val := by omega
      have hs : ¬i.val + 1 ≤ r.val := by omega
      simp [hle, hs, hr]

lemma rootCoordinates_reverse {n : ℕ} (p q : Fin (n + 1)) (t : Fˣ) :
    rootCoordinates F q p t = rootCoordinates F p q t⁻¹ := by
  funext r
  simp only [rootCoordinates_apply, inv_inv]
  exact mul_comm _ _

lemma rootCoordinates_reflect {n : ℕ} (i : Fin n) (p q : Fin (n + 1)) (t : Fˣ) :
    reflectionCoordinates F i (rootCoordinates F p q t) =
      rootCoordinates F (simpleSwap i p) (simpleSwap i q) t := by
  apply diagonalCoordinates_injective F n
  rw [diagonalCoordinates_reflect_swap, diagonalCoordinates_rootCoordinates]
  simp only [diagonalCoordinates_rootCoordinates]
  funext r
  have hp : simpleSwap i r = p ↔ r = simpleSwap i p := by
    constructor <;> intro he
    · rw [← he]
      simp [simpleSwap]
    · rw [he]
      simp [simpleSwap]
  have hq : simpleSwap i r = q ↔ r = simpleSwap i q := by
    constructor <;> intro he
    · rw [← he]
      simp [simpleSwap]
    · rw [he]
      simp [simpleSwap]
  change rootDiagonal F p q t (simpleSwap i r) =
    rootDiagonal F (simpleSwap i p) (simpleSwap i q) t r
  simp only [rootDiagonal, Pi.mul_apply, Pi.mulSingle_apply, hp, hq]

/-- The sign-normalized ordered-pair section; the reversed adjacent section retains {-1,t}. -/
def rootSectionSign {n : ℕ} (p q : Fin (n + 1)) : Fˣ :=
  (-1) ^ p.val * (-1) ^ q.val * (if p < q then -1 else 1)

/-- An actual torus element, with explicit Milnor central coordinate. -/
def rootSection {n : ℕ} (p q : Fin (n + 1)) (t : Fˣ) : Torus F n :=
  coefficient F n (Multiplicative.ofAdd (pair F (rootSectionSign F p q) t)) *
    torusLift F n (rootCoordinates F p q t)

lemma rootSectionSign_simple {n : ℕ} (i : Fin n) :
    rootSectionSign F i.castSucc i.succ = 1 := by
  simp [rootSectionSign, i.castSucc_lt_succ, pow_succ, ← mul_pow]

lemma rootSectionSign_reverse_simple {n : ℕ} (i : Fin n) :
    rootSectionSign F i.succ i.castSucc = -1 := by
  have hnot : ¬i.succ < i.castSucc := not_lt_of_ge i.castSucc_lt_succ.le
  simp [rootSectionSign, hnot, pow_succ, mul_comm, ← mul_pow]

lemma rootSection_simple {n : ℕ} (i : Fin n) (t : Fˣ) :
    rootSection F i.castSucc i.succ t = simple F i t := by
  rw [rootSection, rootSectionSign_simple, pair_one_left, rootCoordinates_simple]
  simp [simple]

lemma rootSection_reverse_simple {n : ℕ} (i : Fin n) (t : Fˣ) :
    rootSection F i.succ i.castSucc t =
      coefficient F n (Multiplicative.ofAdd (pair F (-1) t)) * simple F i t⁻¹ := by
  rw [rootSection, rootSectionSign_reverse_simple, rootCoordinates_reverse,
    rootCoordinates_simple]
  rfl

@[simp] lemma rootSection_diagonal {n : ℕ} (p q : Fin (n + 1)) (t : Fˣ) :
    (rootSection F p q t).diagonal = rootCoordinates F p q t := by
  change 1 * rootCoordinates F p q t = _
  exact one_mul _

@[simp] lemma rootSection_central {n : ℕ} (p q : Fin (n + 1)) (t : Fˣ) :
    (rootSection F p q t).central = pair F (rootSectionSign F p q) t := by
  change pair F (rootSectionSign F p q) t + 0 + cocycle F n 1 _ = _
  simp

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCorootReflection -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

private lemma position_cases {n : ℕ} (i : Fin n) (p : Fin (n + 1)) :
    p.val < i.val ∨ p = i.castSucc ∨ p = i.succ ∨ i.val + 1 < p.val := by
  by_cases h0 : p = i.castSucc
  · exact Or.inr (Or.inl h0)
  by_cases h1 : p = i.succ
  · exact Or.inr (Or.inr (Or.inl h1))
  have hv0 : p.val ≠ i.val := by intro h; exact h0 (Fin.ext h)
  have hv1 : p.val ≠ i.val + 1 := by intro h; exact h1 (Fin.ext h)
  omega

/-- The literal root scaling of the signed matrix W_i(1). -/
def reflectionRootScale {n : ℕ} (i : Fin n) (p q : Fin (n + 1)) : Fˣ :=
  (if p = i.castSucc then -1 else 1) * (if q = i.castSucc then -1 else 1)

/-- The sign recording the central correction on a single ordered root coordinate. -/
def reflectionRootCorrection {n : ℕ} (i : Fin n) (p q : Fin (n + 1)) : Fˣ :=
  (if p = i.succ then -1 else 1) * (if q = i.succ then -1 else 1) *
    (if (p = i.castSucc ∧ q = i.succ) ∨ (p = i.succ ∧ q = i.castSucc) then -1 else 1)

lemma reflectionCorrection_rootCoordinates {n : ℕ} (i : Fin n)
    (p q : Fin (n + 1)) (t : Fˣ) :
    reflectionCorrection F (previous F (rootCoordinates F p q t) i)
      (rootCoordinates F p q t i) (following F (rootCoordinates F p q t) i) =
        pair F (reflectionRootCorrection F i p q) t := by
  rcases position_cases i p with hp | rfl | rfl | hp <;>
    rcases position_cases i q with hq | rfl | rfl | hq
  all_goals
    simp only [reflectionCorrection, previous_rootCoordinates, rootCoordinates_apply,
      following_rootCoordinates, reflectionRootCorrection, Fin.val_castSucc, Fin.val_succ]
    simp (disch := omega) only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ,
      ite_eq_left, ite_eq_right, ↓reduceIte]
  all_goals simp_all [pair_self, pair_skew F (-1) t, pair_sign_neg F t]

lemma rootSectionSign_reflection {n : ℕ} (i : Fin n) (p q : Fin (n + 1)) :
    rootSectionSign F p q * reflectionRootCorrection F i p q =
      reflectionRootScale F i p q * rootSectionSign F (simpleSwap i p) (simpleSwap i q) := by
  rcases position_cases i p with hp | rfl | rfl | hp <;>
    rcases position_cases i q with hq | rfl | rfl | hq
  all_goals
    simp only [rootSectionSign, reflectionRootCorrection, reflectionRootScale,
      simpleSwap, Equiv.swap_apply_def, Fin.val_castSucc, Fin.val_succ]
    simp (disch := omega) only [Fin.ext_iff, Fin.lt_def,
      Fin.val_castSucc, Fin.val_succ, ite_eq_left, ite_eq_right, ↓reduceIte]
  all_goals
    simp_all [pow_succ, mul_comm, ← mul_pow]

/-- Actual frozen reflection transport, with its original central correction. -/
theorem reflection_rootSection {n : ℕ} (i : Fin n) (p q : Fin (n + 1)) (t : Fˣ) :
    reflection F i (rootSection F p q t) =
      coefficient F n (Multiplicative.ofAdd (pair F (reflectionRootScale F i p q) t)) *
        rootSection F (simpleSwap i p) (simpleSwap i q) t := by
  apply Torus.ext
  · change reflectionCoordinates F i (rootSection F p q t).diagonal =
      1 * (rootSection F (simpleSwap i p) (simpleSwap i q) t).diagonal
    rw [rootSection_diagonal, rootSection_diagonal, one_mul, rootCoordinates_reflect]
  · change (rootSection F p q t).central +
      reflectionCorrection F (previous F (rootSection F p q t).diagonal i)
        ((rootSection F p q t).diagonal i)
        (following F (rootSection F p q t).diagonal i) =
      pair F (reflectionRootScale F i p q) t +
        (rootSection F (simpleSwap i p) (simpleSwap i q) t).central + cocycle F n 1 _
    rw [rootSection_central, rootSection_central, rootSection_diagonal,
      cocycle_one_left, add_zero, reflectionCorrection_rootCoordinates,
      ← pair_mul_left, ← pair_mul_left, rootSectionSign_reflection]

end StableSteinberg.RootCoordinate

end

end

/-! ## RootCorootTorus -/

section

open scoped BigOperators

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

/-- The simple coordinate at a matrix position, with value one at the last boundary. -/
def coordinateRight {n : ℕ} (s : Fin n → Fˣ) (r : Fin (n + 1)) : Fˣ :=
  Fin.lastCases 1 s r

/-- The simple coordinate immediately before a matrix position. -/
def coordinateLeft {n : ℕ} (s : Fin n → Fˣ) (r : Fin (n + 1)) : Fˣ :=
  Fin.cases 1 s r

lemma coordinateLeft_castSucc {n : ℕ} (s : Fin n → Fˣ) (i : Fin n) :
    coordinateLeft F s i.castSucc = previous F s i := by
  unfold previous
  by_cases hi : 0 < i.val
  · let j : Fin n := ⟨i.val - 1, by omega⟩
    have he : i.castSucc = j.succ := by apply Fin.ext; dsimp [j]; omega
    simp [hi, he, coordinateLeft, j]
  · have he : i.castSucc = 0 := by apply Fin.ext; simp only [Fin.val_castSucc, Fin.val_zero]; omega
    simp [hi, he, coordinateLeft]

lemma coordinateRight_succ {n : ℕ} (s : Fin n → Fˣ) (i : Fin n) :
    coordinateRight F s i.succ = following F s i := by
  unfold following
  by_cases hi : i.val + 1 < n
  · let j : Fin n := ⟨i.val + 1, hi⟩
    have he : i.succ = j.castSucc := Fin.ext rfl
    simp only [hi, dite_true, coordinateRight, he, Fin.lastCases_castSucc]
    rfl
  · have he : i.succ = Fin.last n := by apply Fin.ext; simp only [Fin.val_succ, Fin.val_last]; omega
    simp [hi, he, coordinateRight]

lemma diagonalCoordinates_position {n : ℕ} (s : Fin n → Fˣ) (r : Fin (n + 1)) :
    diagonalCoordinates F s r = coordinateRight F s r * (coordinateLeft F s r)⁻¹ := by
  cases n with
  | zero =>
    have hr : r = 0 := by apply Fin.ext; have := r.isLt; simp only [Fin.val_zero]; omega
    subst r
    simp only [diagonalCoordinates, Finset.prod_apply, Finset.univ_eq_empty,
      Finset.prod_empty, coordinateRight, coordinateLeft, Fin.cases_zero,
      inv_one, mul_one]
    change (1 : Fˣ) = Fin.lastCases (1 : Fˣ) s (Fin.last 0)
    rw [Fin.lastCases_last]
  | succ n =>
    refine Fin.cases ?_ (fun i => ?_) r
    · have he : (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc := rfl
      rw [he, diagonalCoordinates_castSucc, coordinateLeft_castSucc]
      simp only [coordinateRight, Fin.lastCases_castSucc]
    · rw [diagonalCoordinates_succ, coordinateRight_succ]
      simp [coordinateLeft]

lemma sum_pair_castSucc {n : ℕ} (s : Fin n → Fˣ) (p : Fin (n + 1)) (t : Fˣ) :
    (∑ i : Fin n, pair F (s i) ((Pi.mulSingle p t : Fin (n + 1) → Fˣ) i.castSucc)) =
      pair F (coordinateRight F s p) t := by
  refine Fin.lastCases ?_ (fun j => ?_) p
  · simp [coordinateRight]
  · rw [Finset.sum_eq_single j]
    · simp [coordinateRight]
    · intro k _ hkj
      have he : k.castSucc ≠ j.castSucc := by simpa using hkj
      simp [he]
    · simp

lemma sum_pair_succ {n : ℕ} (s : Fin n → Fˣ) (p : Fin (n + 1)) (t : Fˣ) :
    (∑ i : Fin n, pair F ((Pi.mulSingle p t : Fin (n + 1) → Fˣ) i.succ) (s i)) =
      pair F t (coordinateLeft F s p) := by
  refine Fin.cases ?_ (fun j => ?_) p
  · simp [coordinateLeft]
  · rw [Finset.sum_eq_single j]
    · simp [coordinateLeft]
    · intro k _ hkj
      have he : k.succ ≠ j.succ := by simpa using hkj
      simp [he]
    · simp

lemma cocycle_diagonal_right {n : ℕ} (s v : Fin n → Fˣ) :
    cocycle F n s v = ∑ i : Fin n, pair F (s i) (diagonalCoordinates F v i.castSucc) := by
  rw [cocycle]
  simp_rw [sum_previous]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [diagonalCoordinates_castSucc, pair_mul_right, pair_inv_right]
  exact sub_eq_add_neg _ _

lemma cocycle_diagonal_left {n : ℕ} (s v : Fin n → Fˣ) :
    cocycle F n v s = -(∑ i : Fin n, pair F (diagonalCoordinates F v i.succ) (s i)) := by
  rw [cocycle, Finset.sum_comm]
  simp_rw [sum_following]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [diagonalCoordinates_succ, pair_mul_left, pair_inv_left]
  abel

lemma cocycle_rootCoordinates_right {n : ℕ} (s : Fin n → Fˣ)
    (p q : Fin (n + 1)) (t : Fˣ) :
    cocycle F n s (rootCoordinates F p q t) =
      pair F (coordinateRight F s p * (coordinateRight F s q)⁻¹) t := by
  rw [cocycle_diagonal_right]
  simp_rw [diagonalCoordinates_rootCoordinates, rootDiagonal, Pi.mul_apply, pair_mul_right]
  rw [Finset.sum_add_distrib, sum_pair_castSucc, sum_pair_castSucc,
    pair_inv_right, pair_mul_left, pair_inv_left]

lemma cocycle_rootCoordinates_left {n : ℕ} (s : Fin n → Fˣ)
    (p q : Fin (n + 1)) (t : Fˣ) :
    cocycle F n (rootCoordinates F p q t) s =
      -pair F t (coordinateLeft F s p * (coordinateLeft F s q)⁻¹) := by
  rw [cocycle_diagonal_left]
  simp_rw [diagonalCoordinates_rootCoordinates, rootDiagonal, Pi.mul_apply, pair_mul_left]
  rw [Finset.sum_add_distrib, sum_pair_succ, sum_pair_succ,
    pair_inv_left, pair_mul_right, pair_inv_right]

/-- The full torus commutator pairing is the actual ratio of the two matrix diagonal entries. -/
theorem rootCoordinates_commutator_pairing {n : ℕ} (s : Fin n → Fˣ)
    (p q : Fin (n + 1)) (t : Fˣ) :
    cocycle F n s (rootCoordinates F p q t) - cocycle F n (rootCoordinates F p q t) s =
      pair F (diagonalCoordinates F s p * (diagonalCoordinates F s q)⁻¹) t := by
  rw [cocycle_rootCoordinates_right, cocycle_rootCoordinates_left,
    pair_skew F t, diagonalCoordinates_position, diagonalCoordinates_position]
  simp only [pair_mul_left, pair_inv_left]
  abel

/-- Actual torus conjugation of every marked ordered coroot section. -/
theorem torus_conjugate_rootSection {n : ℕ} (h : Torus F n)
    (p q : Fin (n + 1)) (t : Fˣ) :
    h * rootSection F p q t * h⁻¹ =
      coefficient F n (Multiplicative.ofAdd
        (pair F (diagonalCoordinates F h.diagonal p *
          (diagonalCoordinates F h.diagonal q)⁻¹) t)) * rootSection F p q t := by
  rw [conjugate_formula, rootSection_diagonal, rootCoordinates_commutator_pairing]

end StableSteinberg.RootCoordinate

end

end

/-! ## NormalizerMonomialCoordinates -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
open _root_.Matrix.Bruhat
variable (F : Type u) [Field F]

/-- The row monomial read from the actual normalizer state evaluation. -/
def normalizerMonomialData {n : ℕ} (g : LiftedNormalizer F n) : MonomialGroup F (n + 1) :=
  let s := normalizerEvaluation F n g
  ⟨fun r => diagonalCoordinates F s.1.diagonal r *
    (-1 : Fˣ) ^ _root_.Matrix.GeneralLinearGroup.SignedSection.prefixCount s.2 (s.2.symm r), s.2⟩

lemma normalizerMonomialData_toGL {n : ℕ} (g : LiftedNormalizer F n) :
    monomialToGL F (n + 1) (normalizerMonomialData F g) = normalizerToGL F n g := by
  apply Units.ext
  ext r j
  rw [normalizerToGL_apply, stateMatrix_entry]
  change (if r = (normalizerEvaluation F n g).2 j then
      ((diagonalCoordinates F (normalizerEvaluation F n g).1.diagonal r *
        (-1 : Fˣ) ^ _root_.Matrix.GeneralLinearGroup.SignedSection.prefixCount (normalizerEvaluation
          F n g).2
          ((normalizerEvaluation F n g).2.symm r) : Fˣ) : F) else 0) = _
  by_cases hr : r = (normalizerEvaluation F n g).2 j
  · subst r
    simp
  · simp [hr]

/-- The actual normalizer projection in the original finite monomial coordinates. -/
def normalizerMonomial (n : ℕ) : LiftedNormalizer F n →* MonomialGroup F (n + 1) where
  toFun := normalizerMonomialData F
  map_one' := by
    apply monomialToGL_injective F (n + 1)
    rw [normalizerMonomialData_toGL, map_one, map_one]
  map_mul' g h := by
    apply monomialToGL_injective F (n + 1)
    rw [normalizerMonomialData_toGL, map_mul, map_mul,
      normalizerMonomialData_toGL, normalizerMonomialData_toGL]

@[simp] lemma monomialToGL_normalizerMonomial {n : ℕ} (g : LiftedNormalizer F n) :
    monomialToGL F (n + 1) (normalizerMonomial F n g) = normalizerToGL F n g :=
  normalizerMonomialData_toGL F g

lemma normalizerMonomial_eq_of_toGL {n : ℕ} (g : LiftedNormalizer F n)
    (m : MonomialGroup F (n + 1)) (hm : normalizerToGL F n g = monomialToGL F (n + 1) m) :
    normalizerMonomial F n g = m := by
  apply monomialToGL_injective F (n + 1)
  rw [monomialToGL_normalizerMonomial, hm]

@[simp] lemma normalizerMonomial_torus {n : ℕ} (h : Torus F n) :
    normalizerMonomial F n (normalizerTorus F n h) = ⟨diagonalCoordinates F h.diagonal, 1⟩ := by
  apply monomialToGL_injective F (n + 1)
  rw [monomialToGL_normalizerMonomial, normalizerToGL_torus]
  apply Units.ext
  rfl

/-- The literal diagonal ratio scaling an ordered matrix root under a row monomial. -/
def monomialRootScale {n : ℕ} (m : MonomialGroup F n) (p q : Fin n) : Fˣ :=
  m.left (m.right p) * (m.left (m.right q))⁻¹

@[simp] lemma monomialRootScale_one {n : ℕ} (p q : Fin n) :
    monomialRootScale F (1 : MonomialGroup F n) p q = 1 := by
  simp [monomialRootScale]

lemma monomialRootScale_mul {n : ℕ} (m l : MonomialGroup F n) (p q : Fin n) :
    monomialRootScale F (m * l) p q =
      monomialRootScale F m (l.right p) (l.right q) * monomialRootScale F l p q := by
  change (m.left (m.right (l.right p)) * l.left (m.right.symm (m.right (l.right p)))) *
      (m.left (m.right (l.right q)) * l.left (m.right.symm (m.right (l.right q))))⁻¹ =
    (m.left (m.right (l.right p)) * (m.left (m.right (l.right q)))⁻¹) *
      (l.left (l.right p) * (l.left (l.right q))⁻¹)
  simp [mul_assoc, mul_comm, mul_left_comm]

lemma monomialRootScale_inv {n : ℕ} (m : MonomialGroup F n) (p q : Fin n) :
    monomialRootScale F m⁻¹ (m.right p) (m.right q) = (monomialRootScale F m p q)⁻¹ := by
  have he := monomialRootScale_mul F m⁻¹ m p q
  rw [inv_mul_cancel, monomialRootScale_one] at he
  exact (eq_inv_iff_mul_eq_one).mpr he.symm

/-- The actual monomial coordinates of the literal matrix W_i(1). -/
def reflectionMonomial {n : ℕ} (i : Fin n) : MonomialGroup F (n + 1) :=
  ⟨Pi.mulSingle i.succ (-1), simpleSwap i⟩

lemma reflectionMonomial_toGL {n : ℕ} (i : Fin n) :
    monomialToGL F (n + 1) (reflectionMonomial F i) = simpleWMatrix F i 1 := by
  apply Units.ext
  ext r s
  rw [simpleWMatrix_entry]
  change (if r = (simpleSwap i) s then
    ((Pi.mulSingle i.succ (-1) : Fin (n + 1) → Fˣ) r : F) else 0) = _
  have hij : i.castSucc ≠ i.succ := i.castSucc_lt_succ.ne
  by_cases hri : r = i.castSucc <;> by_cases hrj : r = i.succ <;>
    by_cases hsi : s = i.castSucc <;> by_cases hsj : s = i.succ <;>
      simp_all [simpleSwap, Equiv.swap_apply_def, eq_comm]

@[simp] lemma normalizerMonomial_lambda_inv {n : ℕ} (i : Fin n) :
    normalizerMonomial F n (normalizerLambda F i)⁻¹ = reflectionMonomial F i := by
  apply monomialToGL_injective F (n + 1)
  rw [monomialToGL_normalizerMonomial, ← normalizerW_one, normalizerToGL_W,
    reflectionMonomial_toGL]

lemma monomialRootScale_reflection {n : ℕ} (i : Fin n) (p q : Fin (n + 1)) :
    monomialRootScale F (reflectionMonomial F i) p q = reflectionRootScale F i p q := by
  simp only [monomialRootScale, reflectionMonomial, reflectionRootScale]
  have hs : (simpleSwap i) i.castSucc = i.succ := by simp [simpleSwap]
  have hp : (simpleSwap i) p = i.succ ↔ p = i.castSucc := by
    rw [← hs]
    exact (simpleSwap i).injective.eq_iff
  have hq : (simpleSwap i) q = i.succ ↔ q = i.castSucc := by
    rw [← hs]
    exact (simpleSwap i).injective.eq_iff
  simp only [Pi.mulSingle_apply, hp, hq]
  split_ifs <;> simp

end StableSteinberg.RootCoordinate

end

end

/-! ## NormalizerRootTransport -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
open _root_.Matrix.Bruhat
variable (F : Type u) [Field F]

private lemma normalizerCoefficient_add {n : ℕ} (x y : MilnorKTheory F 2) :
    normalizerCoefficient F n (Multiplicative.ofAdd x) *
      normalizerCoefficient F n (Multiplicative.ofAdd y) =
        normalizerCoefficient F n (Multiplicative.ofAdd (x + y)) :=
  (map_mul (normalizerCoefficient F n) _ _).symm

private lemma normalizerCoefficient_neg {n : ℕ} (x : MilnorKTheory F 2) :
    normalizerCoefficient F n (Multiplicative.ofAdd (-x)) =
      (normalizerCoefficient F n (Multiplicative.ofAdd x))⁻¹ :=
  map_inv (normalizerCoefficient F n) _

lemma normalizer_conjugate_coefficient {n : ℕ} (g : LiftedNormalizer F n)
    (z : Multiplicative (MilnorKTheory F 2)) :
    g * normalizerCoefficient F n z * g⁻¹ = normalizerCoefficient F n z := by
  rw [Subgroup.mem_center_iff.mp (normalizerCoefficient_le_center F n ⟨z, rfl⟩) g,
    mul_inv_cancel_right]

private def RootTransporting {n : ℕ} (g : LiftedNormalizer F n) : Prop :=
  ∀ (p q : Fin (n + 1)) (t : Fˣ),
    g * normalizerTorus F n (rootSection F p q t) * g⁻¹ =
      normalizerCoefficient F n (Multiplicative.ofAdd
        (pair F (monomialRootScale F (normalizerMonomial F n g) p q) t)) *
        normalizerTorus F n (rootSection F ((normalizerMonomial F n g).right p)
          ((normalizerMonomial F n g).right q) t)

private lemma rootTransporting_one (n : ℕ) : RootTransporting F (1 : LiftedNormalizer F n) := by
  intro p q t
  simp [monomialRootScale_one]

private lemma rootTransporting_mul {n : ℕ} (g h : LiftedNormalizer F n)
    (hg : RootTransporting F g) (hh : RootTransporting F h) : RootTransporting F (g * h) := by
  intro p q t
  rw [map_mul, monomialRootScale_mul, SemidirectProduct.mul_right]
  calc
    _ = g * (h * normalizerTorus F n (rootSection F p q t) * h⁻¹) * g⁻¹ := by group
    _ = g * (normalizerCoefficient F n (Multiplicative.ofAdd
        (pair F (monomialRootScale F (normalizerMonomial F n h) p q) t)) *
        normalizerTorus F n (rootSection F ((normalizerMonomial F n h).right p)
          ((normalizerMonomial F n h).right q) t)) * g⁻¹ := by rw [hh p q t]
    _ = (g * normalizerCoefficient F n (Multiplicative.ofAdd
        (pair F (monomialRootScale F (normalizerMonomial F n h) p q) t)) * g⁻¹) *
        (g * normalizerTorus F n (rootSection F ((normalizerMonomial F n h).right p)
          ((normalizerMonomial F n h).right q) t) * g⁻¹) := by group
    _ = _ := by
      rw [normalizer_conjugate_coefficient, hg, ← mul_assoc, normalizerCoefficient_add,
        pair_mul_left, add_comm]
      rfl

private lemma rootTransporting_inv {n : ℕ} (g : LiftedNormalizer F n)
    (hg : RootTransporting F g) : RootTransporting F g⁻¹ := by
  intro p q t
  let m := normalizerMonomial F n g
  let p0 := m.right.symm p
  let q0 := m.right.symm q
  have hp : m.right p0 = p := m.right.apply_symm_apply p
  have hq : m.right q0 = q := m.right.apply_symm_apply q
  have hv := hg p0 q0 t
  change g * normalizerTorus F n (rootSection F p0 q0 t) * g⁻¹ =
    normalizerCoefficient F n (Multiplicative.ofAdd
      (pair F (monomialRootScale F m p0 q0) t)) *
      normalizerTorus F n (rootSection F (m.right p0) (m.right q0) t) at hv
  rw [hp, hq] at hv
  have hs : monomialRootScale F m⁻¹ p q = (monomialRootScale F m p0 q0)⁻¹ := by
    simpa only [hp, hq] using monomialRootScale_inv F m p0 q0
  rw [map_inv, hs, pair_inv_left]
  change g⁻¹ * normalizerTorus F n (rootSection F p q t) * g =
    normalizerCoefficient F n (Multiplicative.ofAdd
      (-pair F (monomialRootScale F m p0 q0) t)) *
      normalizerTorus F n (rootSection F p0 q0 t)
  let z := normalizerCoefficient F n (Multiplicative.ofAdd
    (pair F (monomialRootScale F m p0 q0) t))
  calc
    _ = g⁻¹ * z⁻¹ * (z * normalizerTorus F n (rootSection F p q t)) * g := by group
    _ = g⁻¹ * z⁻¹ * (g * normalizerTorus F n (rootSection F p0 q0 t) * g⁻¹) * g := by
      rw [← hv]
    _ = (g⁻¹ * z⁻¹ * g) * normalizerTorus F n (rootSection F p0 q0 t) := by group
    _ = _ := by
      have hc := normalizer_conjugate_coefficient F g⁻¹
        (Multiplicative.ofAdd (-pair F (monomialRootScale F m p0 q0) t))
      simp only [inv_inv, normalizerCoefficient_neg] at hc
      simpa only [z, normalizerCoefficient_neg] using
        congrArg (fun x => x * normalizerTorus F n (rootSection F p0 q0 t)) hc

private def transportingSubgroup (n : ℕ) : Subgroup (LiftedNormalizer F n) where
  carrier := RootTransporting F
  one_mem' := rootTransporting_one F n
  mul_mem' := fun hg hh => rootTransporting_mul F _ _ hg hh
  inv_mem' := fun hg => rootTransporting_inv F _ hg

private lemma torus_rootTransporting {n : ℕ} (h : Torus F n) :
    RootTransporting F (normalizerTorus F n h) := by
  intro p q t
  rw [normalizerMonomial_torus]
  change normalizerTorus F n h * normalizerTorus F n (rootSection F p q t) *
      (normalizerTorus F n h)⁻¹ =
    normalizerCoefficient F n (Multiplicative.ofAdd
      (pair F (diagonalCoordinates F h.diagonal p *
        (diagonalCoordinates F h.diagonal q)⁻¹) t)) *
      normalizerTorus F n (rootSection F p q t)
  simpa only [map_mul, map_inv, normalizerCoefficient, MonoidHom.comp_apply] using
    congrArg (normalizerTorus F n) (torus_conjugate_rootSection F h p q t)

private lemma lambda_inv_rootTransporting {n : ℕ} (i : Fin n) :
    RootTransporting F (normalizerLambda F i)⁻¹ := by
  intro p q t
  rw [normalizerMonomial_lambda_inv, monomialRootScale_reflection]
  change (normalizerLambda F i)⁻¹ * normalizerTorus F n (rootSection F p q t) *
      normalizerLambda F i =
    normalizerCoefficient F n (Multiplicative.ofAdd
      (pair F (reflectionRootScale F i p q) t)) *
      normalizerTorus F n (rootSection F (simpleSwap i p) (simpleSwap i q) t)
  rw [normalizerLambda_inv_conjugate_torus, reflection_rootSection, map_mul]
  rfl

/-- Uniform marked-coroot transport in the actual generated lifted normalizer. -/
theorem normalizer_conjugate_rootSection {n : ℕ} (g : LiftedNormalizer F n)
    (p q : Fin (n + 1)) (t : Fˣ) :
    g * normalizerTorus F n (rootSection F p q t) * g⁻¹ =
      normalizerCoefficient F n (Multiplicative.ofAdd
        (pair F (monomialRootScale F (normalizerMonomial F n g) p q) t)) *
      normalizerTorus F n (rootSection F ((normalizerMonomial F n g).right p)
        ((normalizerMonomial F n g).right q) t) := by
  have htop : transportingSubgroup F n = ⊤ := by
    apply normalizer_generated F n
    · exact torus_rootTransporting F
    · intro i
      have hi : (normalizerLambda F i)⁻¹ ∈ transportingSubgroup F n :=
        lambda_inv_rootTransporting F i
      simpa only [inv_inv] using (transportingSubgroup F n).inv_mem hi
  have hg : g ∈ transportingSubgroup F n := by rw [htop]; trivial
  exact hg p q t

end StableSteinberg.RootCoordinate

end

end

/-! ## RootTorusTransporter -/

section

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
open _root_.Matrix.Bruhat
variable (F : Type u) [Field F]

/-- Uniform transport with the exact original finite row-monomial matrix coordinates. -/
theorem normalizer_conjugate_rootSection_of_matrix {n : ℕ} (g : LiftedNormalizer F n)
    (m : MonomialGroup F (n + 1))
    (hm : normalizerToGL F n g = monomialToGL F (n + 1) m)
    (p q : Fin (n + 1)) (t : Fˣ) :
    g * normalizerTorus F n (rootSection F p q t) * g⁻¹ =
      normalizerCoefficient F n (Multiplicative.ofAdd
        (pair F (monomialRootScale F m p q) t)) *
      normalizerTorus F n (rootSection F (m.right p) (m.right q) t) := by
  have he := normalizer_conjugate_rootSection F g p q t
  rw [normalizerMonomial_eq_of_toGL F g m hm] at he
  exact he

/-- Equal orientation has the positive symbol of the literal row-weight ratio. -/
theorem normalizer_conjugate_simple_equal {n : ℕ} (i k : Fin n)
    (g : LiftedNormalizer F n) (m : MonomialGroup F (n + 1))
    (hm : normalizerToGL F n g = monomialToGL F (n + 1) m)
    (hk : m.right k.castSucc = i.castSucc) (hl : m.right k.succ = i.succ) (t : Fˣ) :
    g * normalizerTorus F n (simple F k t) * g⁻¹ =
      normalizerCoefficient F n (Multiplicative.ofAdd
        (pair F (m.left i.castSucc * (m.left i.succ)⁻¹) t)) *
      normalizerTorus F n (simple F i t) := by
  have he := normalizer_conjugate_rootSection_of_matrix F g m hm k.castSucc k.succ t
  simpa only [rootSection_simple, monomialRootScale, hk, hl] using he

/-- Opposite orientation retains the exact sign in f=-d_i/d_(i+1). -/
theorem normalizer_conjugate_simple_opposite {n : ℕ} (i k : Fin n)
    (g : LiftedNormalizer F n) (m : MonomialGroup F (n + 1))
    (hm : normalizerToGL F n g = monomialToGL F (n + 1) m)
    (hk : m.right k.castSucc = i.succ) (hl : m.right k.succ = i.castSucc) (t : Fˣ) :
    g * normalizerTorus F n (simple F k t) * g⁻¹ =
      normalizerCoefficient F n (Multiplicative.ofAdd
        (pair F (-m.left i.castSucc * (m.left i.succ)⁻¹)⁻¹ t)) *
      normalizerTorus F n (simple F i t⁻¹) := by
  let r := m.left i.succ * (m.left i.castSucc)⁻¹
  have hunit : r * (-1) = (-m.left i.castSucc * (m.left i.succ)⁻¹)⁻¹ := by
    simp [r, mul_comm]
  calc
    _ = normalizerCoefficient F n (Multiplicative.ofAdd (pair F r t)) *
        normalizerTorus F n (rootSection F i.succ i.castSucc t) := by
      simpa only [rootSection_simple, monomialRootScale, hk, hl] using
        normalizer_conjugate_rootSection_of_matrix F g m hm k.castSucc k.succ t
    _ = normalizerCoefficient F n (Multiplicative.ofAdd (pair F r t)) *
        (normalizerCoefficient F n (Multiplicative.ofAdd (pair F (-1) t)) *
          normalizerTorus F n (simple F i t⁻¹)) := by
      rw [rootSection_reverse_simple, map_mul]
      rfl
    _ = _ := by
      rw [← mul_assoc, ← map_mul]
      change normalizerCoefficient F n
        (Multiplicative.ofAdd (pair F r t + pair F (-1) t)) * _ = _
      rw [← pair_mul_left, hunit]

/-- The rank-one sign calibration gives f=a², exactly as the literal Weyl matrix does. -/
theorem normalizerW_conjugate_simple {n : ℕ} (i : Fin n) (a t : Fˣ) :
    normalizerW F i a * normalizerTorus F n (simple F i t) * (normalizerW F i a)⁻¹ =
      normalizerCoefficient F n (Multiplicative.ofAdd (pair F (a ^ 2)⁻¹ t)) *
        normalizerTorus F n (simple F i t⁻¹) := by
  rw [normalizerW_conjugate_torus, reflection_simple_self, conjugate_formula]
  have he : cocycle F n (simple F i a).diagonal (simple F i t⁻¹).diagonal -
      cocycle F n (simple F i t⁻¹).diagonal (simple F i a).diagonal =
        pair F (a ^ 2)⁻¹ t := by
    change cocycle F n (Pi.mulSingle i a) (Pi.mulSingle i t⁻¹) -
      cocycle F n (Pi.mulSingle i t⁻¹) (Pi.mulSingle i a) = _
    rw [cocycle_single_single, cocycle_single_single, pair_skew F t⁻¹ a]
    simp only [pair_inv_left, pair_inv_right, pow_two, pair_mul_left]
    abel
  rw [he, map_mul]
  rfl

/-- The diagonal specialization retains the original positive ratio symbol. -/
theorem normalizerTorus_conjugate_simple {n : ℕ} (h : Torus F n) (i : Fin n) (t : Fˣ) :
    normalizerTorus F n h * normalizerTorus F n (simple F i t) *
      (normalizerTorus F n h)⁻¹ =
      normalizerCoefficient F n (Multiplicative.ofAdd
        (pair F (diagonalCoordinates F h.diagonal i.castSucc *
          (diagonalCoordinates F h.diagonal i.succ)⁻¹) t)) *
        normalizerTorus F n (simple F i t) := by
  have he := congrArg (normalizerTorus F n)
    (torus_conjugate_rootSection F h i.castSucc i.succ t)
  simpa only [rootSection_simple, map_mul, map_inv, normalizerCoefficient,
    MonoidHom.comp_apply] using he

end StableSteinberg.RootCoordinate

end

end
