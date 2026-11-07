/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, kangxyz
-/
module

public import Colib.GroupTheory.Steinberg.Matsumoto.LiftedWeyl
public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.SignedSection
public import Mathlib.Order.Fin.Basic
public import Colib.GroupTheory.Steinberg.Matsumoto.Normalizer
public import Colib.GroupTheory.Steinberg.Matsumoto.Torus
public import Colib.GroupTheory.Steinberg.Matsumoto.Weyl
public import Colib.GroupTheory.Steinberg.Matsumoto.NormalizerMatrix
public import Colib.GroupTheory.Steinberg.Matsumoto.MatrixBasics
public import Colib.LinearAlgebra.Matrix.Bruhat.Coordinates

/-!
# WeylTransporter

Adapted from Quillen Matsumoto/WeylTransporter.lean at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using the native Stacks
homogeneous Milnor group and native matrix units throughout.

The declarations retain their original field, rank, central-kernel and explicit
transport hypotheses. Their current consumer is the finite Matsumoto normalizer,
Bruhat action, or conditional original-root detector construction.
-/

@[expose] public section

/-! ## WeylInversions -/

section

/-!
# Finite type-A inversion length

This counts literal inversions and proves the adjacent ascent recurrence.
-/

noncomputable section
namespace StableSteinberg.RootCoordinate
open _root_.Matrix.GeneralLinearGroup.SignedSection

/-- The number of inversions of a finite permutation. -/
def inversionLength {m : ℕ} (σ : Equiv.Perm (Fin m)) : ℕ :=
  ∑ j, prefixCount σ j

@[simp] lemma inversionLength_one (m : ℕ) :
    inversionLength (1 : Equiv.Perm (Fin m)) = 0 := by
  simp [inversionLength]

lemma inversionLength_eq_sum {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    inversionLength σ = ∑ j, ∑ k, if k < j ∧ σ j < σ k then 1 else 0 := by
  classical
  simp only [inversionLength, prefixCount, prefixSet, Finset.card_eq_sum_ones,
    Finset.sum_filter]

lemma inversionLength_inv {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    inversionLength σ⁻¹ = inversionLength σ := by
  classical
  rw [inversionLength_eq_sum, inversionLength_eq_sum]
  calc
    _ = ∑ j, ∑ k, if σ k < σ j ∧ j < k then 1 else 0 := by
      symm
      apply Fintype.sum_equiv σ
      intro j
      apply Fintype.sum_equiv σ
      intro k
      simp
    _ = ∑ k, ∑ j, if σ k < σ j ∧ j < k then 1 else 0 := Finset.sum_comm
    _ = _ := by simp only [and_comm]

lemma prefixCount_ascent {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n)
    (ha : isAscent i σ) (j : Fin (n + 1)) :
    prefixCount (simpleSwap i * σ) j = prefixCount σ j +
      if j = σ.symm i.succ then 1 else 0 := by
  classical
  change σ.symm i.castSucc < σ.symm i.succ at ha
  by_cases hjb : σ j = i.succ
  · have he : j = σ.symm i.succ := by simpa using congrArg σ.symm hjb
    have hp : σ⁻¹ i.castSucc < j := by simpa [he] using ha
    have hv := prefixCount_upper σ i j hjb
    rw [ite_eq_left hp] at hv
    simpa only [simpleSwap, adjacentSwap, ite_eq_left he] using hv
  · have he : j ≠ σ.symm i.succ := by
      intro h
      apply hjb
      simp [h]
    by_cases hja : σ j = i.castSucc
    · have hej : j = σ.symm i.castSucc := by simpa using congrArg σ.symm hja
      have hp : ¬ σ⁻¹ i.succ < j := by
        simpa [hej] using not_lt_of_gt ha
      have hv := prefixCount_lower σ i j hja
      simp only [ite_eq_right hp, Nat.add_zero] at hv
      simpa only [simpleSwap, adjacentSwap, ite_eq_right he, Nat.add_zero] using hv.symm
    · simpa [simpleSwap, adjacentSwap, he] using prefixCount_away σ i j hja hjb

lemma inversionLength_left_ascent {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n)
    (ha : isAscent i σ) :
    inversionLength (simpleSwap i * σ) = inversionLength σ + 1 := by
  classical
  unfold inversionLength
  simp_rw [prefixCount_ascent σ i ha]
  rw [Finset.sum_add_distrib]
  simp

lemma inversionLength_left_descent {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n)
    (ha : ¬isAscent i σ) :
    inversionLength σ = inversionLength (simpleSwap i * σ) + 1 := by
  have he := inversionLength_left_ascent (simpleSwap i * σ) i
    ((isAscent_toggle i σ).mpr ha)
  simpa only [← mul_assoc, simpleSwap_mul_self, one_mul] using he

lemma inversionLength_left_le {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n) :
    inversionLength (simpleSwap i * σ) ≤ inversionLength σ + 1 := by
  by_cases ha : isAscent i σ
  · exact (inversionLength_left_ascent σ i ha).le
  · have he := inversionLength_left_descent σ i ha
    omega

lemma inversionLength_right_ascent {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (k : Fin n)
    (ha : σ k.castSucc < σ k.succ) :
    inversionLength (σ * simpleSwap k) = inversionLength σ + 1 := by
  have he := inversionLength_left_ascent σ⁻¹ k (by exact ha)
  have hinv : (σ * simpleSwap k)⁻¹ = simpleSwap k * σ⁻¹ := by
    simp [_root_.mul_inv_rev, simpleSwap]
  rw [← inversionLength_inv (σ * simpleSwap k), hinv, he, inversionLength_inv]

lemma permutation_eq_one_of_all_ascents {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (ha : ∀ i : Fin n, isAscent i σ) : σ = 1 := by
  have hm : StrictMono σ.symm := Fin.strictMono_iff_lt_succ.mpr ha
  have hm' : StrictMono σ := by
    intro a b hab
    exact hm.lt_iff_lt.mp (by simpa using hab)
  ext j
  exact le_antisymm (by simpa using hm.id_le (σ j)) (hm'.id_le j)

end StableSteinberg.RootCoordinate

end

end

/-! ## WeylPositiveWords -/

section

/-!
# Positive adjacent words in the actual lifted normalizer

Inversion length supplies ascending words without invoking a generic reduced-word theorem.
The regular state action then identifies all minimal positive words.
-/

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate

/-- The permutation represented by a finite positive adjacent word. -/
def adjacentWordPermutation {n : ℕ} (w : List (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  (w.map simpleSwap).prod

@[simp] lemma adjacentWordPermutation_nil (n : ℕ) :
    adjacentWordPermutation ([] : List (Fin n)) = 1 := rfl

@[simp] lemma adjacentWordPermutation_cons {n : ℕ} (i : Fin n) (w : List (Fin n)) :
    adjacentWordPermutation (i :: w) = simpleSwap i * adjacentWordPermutation w := rfl

lemma adjacentWordPermutation_append {n : ℕ} (w v : List (Fin n)) :
    adjacentWordPermutation (w ++ v) = adjacentWordPermutation w * adjacentWordPermutation v := by
  simp [adjacentWordPermutation]

lemma inversionLength_word_le {n : ℕ} (w : List (Fin n)) :
    inversionLength (adjacentWordPermutation w) ≤ w.length := by
  induction w with
  | nil => simp
  | cons i w ih =>
      rw [adjacentWordPermutation_cons, List.length_cons]
      exact (inversionLength_left_le _ i).trans (Nat.add_le_add_right ih 1)

/-- Finite descent sorting gives an adjacent word with precisely the inversion length. -/
theorem exists_minimal_adjacent_word {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    ∃ w : List (Fin n), adjacentWordPermutation w = σ ∧ w.length = inversionLength σ := by
  classical
  induction hl : inversionLength σ using Nat.strong_induction_on generalizing σ with
  | h m ih =>
      by_cases he : σ = 1
      · exact ⟨[], by simp [he], by simpa [he] using hl⟩
      · have hd : ∃ i : Fin n, ¬isAscent i σ := by
          by_contra h
          exact he (permutation_eq_one_of_all_ascents σ (by simpa using h))
        obtain ⟨i, hi⟩ := hd
        have hstep := inversionLength_left_descent σ i hi
        obtain ⟨w, hw, hlen⟩ := ih (inversionLength (simpleSwap i * σ)) (by omega)
          (simpleSwap i * σ) rfl
        refine ⟨i :: w, ?_, ?_⟩
        · rw [adjacentWordPermutation_cons, hw, ← mul_assoc, simpleSwap_mul_self, one_mul]
        · simp only [List.length_cons, hlen]
          exact hstep.symm.trans hl

variable (F : Type u) [Field F]

/-- The same finite positive word in actual lifted Weyl generators. -/
def adjacentWordLift {n : ℕ} (w : List (Fin n)) : LiftedNormalizer F n :=
  (w.map (normalizerLambda F)).prod

@[simp] lemma adjacentWordLift_nil (n : ℕ) :
    adjacentWordLift F ([] : List (Fin n)) = 1 := rfl

@[simp] lemma adjacentWordLift_cons {n : ℕ} (i : Fin n) (w : List (Fin n)) :
    adjacentWordLift F (i :: w) = normalizerLambda F i * adjacentWordLift F w := rfl

lemma adjacentWordLift_append {n : ℕ} (w v : List (Fin n)) :
    adjacentWordLift F (w ++ v) = adjacentWordLift F w * adjacentWordLift F v := by
  simp [adjacentWordLift]

/-- The canonical element whose regular state is the pure permutation. -/
def pureNormalizerLift {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) : LiftedNormalizer F n :=
  (normalizerStateEquiv F n).symm (1, σ)

@[simp] lemma normalizerEvaluation_pure {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    normalizerEvaluation F n (pureNormalizerLift F σ) = (1, σ) :=
  (normalizerStateEquiv F n).apply_symm_apply (1, σ)

/-- Minimal positive words take only ascent branches in the literal state action. -/
theorem normalizerEvaluation_minimal_word {n : ℕ} (w : List (Fin n))
    (hlen : inversionLength (adjacentWordPermutation w) = w.length) :
    normalizerEvaluation F n (adjacentWordLift F w) = (1, adjacentWordPermutation w) := by
  classical
  induction w with
  | nil => rfl
  | cons i w ih =>
      have hb := inversionLength_word_le w
      have ha : isAscent i (adjacentWordPermutation w) := by
        by_contra hn
        have hd := inversionLength_left_descent (adjacentWordPermutation w) i hn
        simp only [adjacentWordPermutation_cons, List.length_cons] at hlen
        omega
      have hs := inversionLength_left_ascent (adjacentWordPermutation w) i ha
      have hw : inversionLength (adjacentWordPermutation w) = w.length := by
        simp only [adjacentWordPermutation_cons, List.length_cons] at hlen
        omega
      rw [adjacentWordLift_cons, adjacentWordPermutation_cons]
      change liftedWeyl F i (normalizerEvaluation F n (adjacentWordLift F w)) = _
      rw [ih hw]
      simp [liftedWeyl, descentCarry, ha]

lemma adjacentWordLift_eq_pure {n : ℕ} (w : List (Fin n))
    (hlen : inversionLength (adjacentWordPermutation w) = w.length) :
    adjacentWordLift F w = pureNormalizerLift F (adjacentWordPermutation w) := by
  apply normalizerEvaluation_injective F n
  rw [normalizerEvaluation_minimal_word F w hlen, normalizerEvaluation_pure]

lemma lambda_mul_pure_ascent {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n)
    (ha : isAscent i σ) :
    normalizerLambda F i * pureNormalizerLift F σ =
      pureNormalizerLift F (simpleSwap i * σ) := by
  classical
  apply normalizerEvaluation_injective F n
  change liftedWeyl F i (normalizerEvaluation F n (pureNormalizerLift F σ)) = _
  rw [normalizerEvaluation_pure, normalizerEvaluation_pure]
  simp [liftedWeyl, descentCarry, ha]

/-- A right ascent also concatenates pure lifts, proved from finite inversion counting. -/
theorem pure_mul_lambda_ascent {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (k : Fin n)
    (ha : σ k.castSucc < σ k.succ) :
    pureNormalizerLift F σ * normalizerLambda F k =
      pureNormalizerLift F (σ * simpleSwap k) := by
  obtain ⟨w, hw, hlen⟩ := exists_minimal_adjacent_word σ
  have he : adjacentWordLift F w = pureNormalizerLift F σ := by
    rw [adjacentWordLift_eq_pure F w (by rw [hw, hlen]), hw]
  have hperm : adjacentWordPermutation (w ++ [k]) = σ * simpleSwap k := by
    simp [adjacentWordPermutation_append, hw]
  have hcount : inversionLength (adjacentWordPermutation (w ++ [k])) = (w ++ [k]).length := by
    rw [hperm, inversionLength_right_ascent σ k ha, List.length_append, hlen]
    rfl
  have hfinal := adjacentWordLift_eq_pure F (w ++ [k]) hcount
  simpa only [adjacentWordLift_append, adjacentWordLift_cons, adjacentWordLift_nil,
    mul_one, he, hperm] using hfinal

end StableSteinberg.RootCoordinate

end

end

/-! ## WeylPureTransport -/

section

/-!
# Pure lift transport of a positive adjacent pair

Finite ascent words and regular evaluation prove the literal conjugacy in the normalizer.
-/

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate

lemma permutation_intertwines_simpleSwap {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (i k : Fin n) (h0 : σ k.castSucc = i.castSucc) (h1 : σ k.succ = i.succ) :
    simpleSwap i * σ = σ * simpleSwap k := by
  apply Equiv.ext
  intro j
  simpa only [Equiv.Perm.mul_apply, simpleSwap, h0, h1] using
    σ.injective.swap_apply k.castSucc k.succ j

/-- The literal signed section has equal signs on a positive adjacent source-image pair. -/
lemma prefixCount_positive_adjacent {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (i k : Fin n) (h0 : σ k.castSucc = i.castSucc) (h1 : σ k.succ = i.succ) :
    _root_.Matrix.GeneralLinearGroup.SignedSection.prefixCount σ k.castSucc =
      _root_.Matrix.GeneralLinearGroup.SignedSection.prefixCount σ k.succ := by
  apply congrArg Finset.card
  ext j
  rw [_root_.Matrix.GeneralLinearGroup.SignedSection.mem_prefixSet,
    _root_.Matrix.GeneralLinearGroup.SignedSection.mem_prefixSet, h0, h1]
  by_cases hj0 : j = k.castSucc
  · subst j
    simp [h0, not_lt_of_ge i.castSucc_lt_succ.le]
  by_cases hj1 : j = k.succ
  · subst j
    simp [not_lt_of_ge k.castSucc_lt_succ.le]
  have hjv : j.val ≠ k.val := by
    intro he
    exact hj0 (Fin.ext he)
  have hσv : (σ j).val ≠ i.val + 1 := by
    intro he
    have he' : σ j = i.succ := Fin.ext he
    exact hj1 (σ.injective (he'.trans h1.symm))
  simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
  omega

variable (F : Type u) [Field F]

/-- Transport of W_k(-1) by the actual pure lift when its ordered pair stays adjacent. -/
theorem pureNormalizerLift_intertwines_lambda {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (i k : Fin n)
    (h0 : σ k.castSucc = i.castSucc) (h1 : σ k.succ = i.succ) :
    pureNormalizerLift F σ * normalizerLambda F k =
      normalizerLambda F i * pureNormalizerLift F σ := by
  have hr : σ k.castSucc < σ k.succ := by rw [h0, h1]; exact i.castSucc_lt_succ
  have hl : isAscent i σ := by
    change σ.symm i.castSucc < σ.symm i.succ
    rw [← h0, ← h1, σ.symm_apply_apply, σ.symm_apply_apply]
    exact k.castSucc_lt_succ
  rw [pure_mul_lambda_ascent F σ k hr, lambda_mul_pure_ascent F σ i hl,
    permutation_intertwines_simpleSwap σ i k h0 h1]

/-- The actual regular normal form factors as its torus state times its pure permutation. -/
lemma normalizer_eq_torus_mul_pure {n : ℕ} (g : LiftedNormalizer F n) :
    g = normalizerTorus F n (normalizerEvaluation F n g).1 *
      pureNormalizerLift F (normalizerEvaluation F n g).2 := by
  apply normalizerEvaluation_injective F n
  change normalizerEvaluation F n g = torusLeft F n (normalizerEvaluation F n g).1
    (normalizerEvaluation F n (pureNormalizerLift F (normalizerEvaluation F n g).2))
  rw [normalizerEvaluation_pure]
  change normalizerEvaluation F n g =
    ((normalizerEvaluation F n g).1 * 1, (normalizerEvaluation F n g).2)
  simp

end StableSteinberg.RootCoordinate

end

end

/-! ## WeylTorusTransport -/

section

/-!
# Actual torus transport of the normalized Weyl element

The coefficient in the Milnor kernel is retained in the calculation.
-/

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

lemma transport_pair_identity (l x r : Fˣ) :
    pair F x (-1) - pair F r (-1) =
      reflectionCorrection F l x r +
        (pair F (-(l * x⁻¹ * r * x⁻¹)⁻¹) (l * x⁻¹ * r) -
          pair F (-(l * x⁻¹ * r * x⁻¹)⁻¹) l) := by
  rw [neg_eq_neg_one_mul ((l * x⁻¹ * r * x⁻¹)⁻¹)]
  simp only [reflectionCorrection, pair_mul_left, pair_mul_right,
    pair_inv_left, pair_inv_right, pair_self]
  rw [pair_skew F (-1) l, pair_skew F (-1) x, pair_skew F (-1) r,
    pair_skew F x l, pair_skew F r l, pair_skew F r x]
  apply eq_of_sub_eq_zero
  calc
    _ = (pair F x (-1) + pair F x (-1)) +
        (pair F r (-1) + pair F r (-1)) := by abel
    _ = 0 := by rw [pair_sign_two, pair_sign_two, add_zero]

lemma torus_transport_reflection {n : ℕ} (i : Fin n) (h : Torus F n) :
    h * simple F i (-1) =
      simple F i (-(reflectionDelta F i h.diagonal)⁻¹) * reflection F i h := by
  apply Torus.ext
  · change h.diagonal * Pi.mulSingle i (-1) =
      Pi.mulSingle i (-(reflectionDelta F i h.diagonal)⁻¹) *
        reflectionCoordinates F i h.diagonal
    rw [reflectionCoordinates]
    ext j
    by_cases hj : j = i
    · subst j
      simp [mul_comm, mul_left_comm]
    · simp [hj]
  · change h.central + 0 + cocycle F n h.diagonal (Pi.mulSingle i (-1)) =
      0 + (h.central + reflectionCorrection F (previous F h.diagonal i)
        (h.diagonal i) (following F h.diagonal i)) +
          cocycle F n (Pi.mulSingle i (-(reflectionDelta F i h.diagonal)⁻¹))
            (reflectionCoordinates F i h.diagonal)
    rw [cocycle_single_right, cocycle_single_left, reflectionCoordinates_self,
      previous_reflection]
    have he := transport_pair_identity F (previous F h.diagonal i)
      (h.diagonal i) (following F h.diagonal i)
    dsimp [reflectionDelta]
    rw [he]
    abel

/-- The diagonal ratio of the two rows affected by the actual simple Weyl element. -/
def torusRootRatio {n : ℕ} (i : Fin n) (h : Torus F n) : Fˣ :=
  diagonalCoordinates F h.diagonal i.castSucc *
    (diagonalCoordinates F h.diagonal i.succ)⁻¹

lemma torusRootRatio_eq_delta_inv {n : ℕ} (i : Fin n) (h : Torus F n) :
    torusRootRatio F i h = (reflectionDelta F i h.diagonal)⁻¹ := by
  rw [torusRootRatio, diagonalCoordinates_castSucc, diagonalCoordinates_succ]
  simp [reflectionDelta, mul_comm, mul_left_comm]

/-- Conjugation in the actual lifted normalizer, rather than merely its matrix image. -/
theorem normalizerTorus_conjugate_lambda {n : ℕ} (i : Fin n) (h : Torus F n) :
    normalizerTorus F n h * normalizerLambda F i * (normalizerTorus F n h)⁻¹ =
      normalizerW F i (-torusRootRatio F i h) := by
  have ht : h * (theta F i h)⁻¹ * simple F i (-1) =
      simple F i (-torusRootRatio F i h) := by
    have he := torus_transport_reflection F i h
    rw [← torusRootRatio_eq_delta_inv] at he
    have htheta : theta F i h =
        simple F i (-1) * reflection F i h * (simple F i (-1))⁻¹ := by
      simpa only [theta, MulEquiv.symm_apply_apply] using
        theta_square F i (reflection F i h)
    rw [htheta]
    calc
      _ = (h * simple F i (-1)) * (reflection F i h)⁻¹ := by group
      _ = _ := by rw [he]; group
  apply (mul_left_inj (normalizerLambda F i)).mp
  rw [normalizerW, inv_mul_cancel_right, ← map_inv]
  calc
    _ = normalizerTorus F n h *
        (normalizerLambda F i * normalizerTorus F n h⁻¹) * normalizerLambda F i := by
      group
    _ = normalizerTorus F n h * normalizerTorus F n (theta F i h⁻¹) *
        (normalizerLambda F i * normalizerLambda F i) := by
      rw [normalizerLambda_mul_torus]
      group
    _ = _ := by
      rw [normalizerLambda_square, ← map_mul, ← map_mul, map_inv, ht]

end StableSteinberg.RootCoordinate

end

end

/-! ## WeylRowTransport -/

section

/-!
# Actual lifted Weyl transport from literal row-monomial matrix data

The matrix data determines the permutation and root ratio. The equality itself is proved
in the lifted normalizer by the regular normal form, with the Milnor kernel retained.
-/

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
variable (F : Type u) [Field F]

lemma normalizerEvaluation_permutation_of_rows {n : ℕ} (g : LiftedNormalizer F n)
    (σ : Equiv.Perm (Fin (n + 1))) (d : Fin (n + 1) → Fˣ)
    (hm : ∀ r j, (normalizerToGL F n g).val r j =
      if r = σ j then (d r : F) else 0) :
    (normalizerEvaluation F n g).2 = σ := by
  apply Equiv.ext
  intro j
  by_contra hn
  have he := hm ((normalizerEvaluation F n g).2 j) j
  rw [normalizerToGL_apply, stateMatrix_entry] at he
  simp [hn] at he

lemma normalizerEvaluation_rows {n : ℕ} (g : LiftedNormalizer F n)
    (σ : Equiv.Perm (Fin (n + 1))) (d : Fin (n + 1) → Fˣ)
    (hm : ∀ r j, (normalizerToGL F n g).val r j =
      if r = σ j then (d r : F) else 0) (r : Fin (n + 1)) :
    diagonalCoordinates F (normalizerEvaluation F n g).1.diagonal r *
      (-1 : Fˣ) ^ _root_.Matrix.GeneralLinearGroup.SignedSection.prefixCount σ (σ.symm r) = d r :=
        by
  have hs := normalizerEvaluation_permutation_of_rows F g σ d hm
  apply Units.ext
  have he := hm r (σ.symm r)
  rw [normalizerToGL_apply, stateMatrix_entry, hs] at he
  simpa using he

lemma normalizerEvaluation_rootRatio_of_rows {n : ℕ} (g : LiftedNormalizer F n)
    (σ : Equiv.Perm (Fin (n + 1))) (d : Fin (n + 1) → Fˣ)
    (hm : ∀ r j, (normalizerToGL F n g).val r j =
      if r = σ j then (d r : F) else 0)
    (i k : Fin n) (h0 : σ k.castSucc = i.castSucc) (h1 : σ k.succ = i.succ) :
    torusRootRatio F i (normalizerEvaluation F n g).1 = d i.castSucc * (d i.succ)⁻¹ := by
  have hi0 : σ.symm i.castSucc = k.castSucc := by rw [← h0, σ.symm_apply_apply]
  have hi1 : σ.symm i.succ = k.succ := by rw [← h1, σ.symm_apply_apply]
  rw [← normalizerEvaluation_rows F g σ d hm i.castSucc,
    ← normalizerEvaluation_rows F g σ d hm i.succ, hi0, hi1,
    prefixCount_positive_adjacent σ i k h0 h1]
  simp [torusRootRatio, mul_comm, mul_left_comm, mul_assoc]

/-- Actual-N transport of the signed Weyl generator under positive adjacent root transport. -/
theorem normalizer_conjugate_W_neg_one_of_rows {n : ℕ} (g : LiftedNormalizer F n)
    (σ : Equiv.Perm (Fin (n + 1))) (d : Fin (n + 1) → Fˣ)
    (hm : ∀ r j, (normalizerToGL F n g).val r j =
      if r = σ j then (d r : F) else 0)
    (i k : Fin n) (h0 : σ k.castSucc = i.castSucc) (h1 : σ k.succ = i.succ) :
    g * normalizerW F k (-1) * g⁻¹ =
      normalizerW F i (-(d i.castSucc * (d i.succ)⁻¹)) := by
  have hs := normalizerEvaluation_permutation_of_rows F g σ d hm
  have hc := normalizerEvaluation_rootRatio_of_rows F g σ d hm i k h0 h1
  have hp := pureNormalizerLift_intertwines_lambda F σ i k h0 h1
  have hg := normalizer_eq_torus_mul_pure F g
  rw [hs] at hg
  rw [normalizerW_neg_one, hg]
  calc
    _ = normalizerTorus F n (normalizerEvaluation F n g).1 *
        (pureNormalizerLift F σ * normalizerLambda F k) *
        (pureNormalizerLift F σ)⁻¹ *
        (normalizerTorus F n (normalizerEvaluation F n g).1)⁻¹ := by group
    _ = normalizerTorus F n (normalizerEvaluation F n g).1 * normalizerLambda F i *
        (normalizerTorus F n (normalizerEvaluation F n g).1)⁻¹ := by rw [hp]; group
    _ = _ := by rw [normalizerTorus_conjugate_lambda, hc]

end StableSteinberg.RootCoordinate

end

end

/-! ## WeylTransporter -/

section

/-!
# Weyl transporter for the actual lifted normalizer

This adapter uses only the literal monomial matrix definition. All lifted-group equality
comes from the proved row-data transporter, not from a comparison with a different extension.
-/

noncomputable section
universe u
namespace StableSteinberg.RootCoordinate
open _root_.Matrix.Bruhat
variable (F : Type u) [Field F]

/-- The requested transporter identity in the actual normalizer, with no symbol quotient. -/
theorem normalizer_conjugate_W_neg_one {n : ℕ} (g : LiftedNormalizer F n)
    (m : MonomialGroup F (n + 1))
    (hm : normalizerToGL F n g = monomialToGL F (n + 1) m)
    (i k : Fin n) (h0 : m.right k.castSucc = i.castSucc) (h1 : m.right k.succ = i.succ) :
    g * normalizerW F k (-1) * g⁻¹ =
      normalizerW F i (-(m.left i.castSucc * (m.left i.succ)⁻¹)) := by
  apply normalizer_conjugate_W_neg_one_of_rows F g m.right m.left ?_ i k h0 h1
  intro r j
  rw [hm]
  rfl

end StableSteinberg.RootCoordinate

end

end
