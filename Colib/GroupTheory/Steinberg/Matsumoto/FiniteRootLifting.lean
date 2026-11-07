/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, kangxyz
-/
module

public import Colib.GroupTheory.MonoidHom.CentralKernel
public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# FiniteRootLifting

Adapted from `Quillen/Algebra/Group/StableSteinberg/Matsumoto/FiniteRootLifting.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual maps and hypotheses.

The declarations retain their original field, rank, central-kernel and explicit
transport hypotheses. Their current consumer is the finite Matsumoto normalizer,
Bruhat action, or conditional original-root detector construction.
-/

@[expose] public section

/-! ## FiniteRootLifting -/

section

open scoped BigOperators commutatorElement

noncomputable section
universe u v

namespace StableSteinberg.FiniteRootLifting

variable (F : Type u) [Field F]

/-- An actual invertible diagonal matrix, with its literal diagonal inverse. -/
def diagonalUnit {n : ℕ} (w : Fin n → Fˣ) : Matrix.GeneralLinearGroup (Fin n) F where
  val := Matrix.diagonal (fun i => (w i : F))
  inv := Matrix.diagonal (fun i => ((w i)⁻¹ : Fˣ))
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_one]
    funext i
    simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_one]
    funext i
    simp

@[simp] lemma diagonalUnit_val {n : ℕ} (w : Fin n → Fˣ) :
    (diagonalUnit F w).val = Matrix.diagonal (fun i => (w i : F)) := rfl

/-- A product-one tuple really gives a determinant-one matrix. -/
theorem diagonalUnit_det {n : ℕ} (w : Fin n → Fˣ) (hw : ∏ i, w i = 1) :
    Matrix.GeneralLinearGroup.det (diagonalUnit F w) = 1 := by
  apply Units.ext
  change Matrix.det (Matrix.diagonal (fun i => (w i : F))) = 1
  rw [Matrix.det_diagonal]
  simpa only [Units.coe_prod, Units.val_one] using congrArg (fun x : Fˣ => (x : F)) hw

/-- The weight ratio is the literal coefficient in diagonal matrix conjugation. -/
theorem diagonalUnit_conjugate_unit {n : ℕ} (w : Fin n → Fˣ)
    (i j : Fin n) (hij : i ≠ j) (a : F) :
    diagonalUnit F w * _root_.Matrix.GeneralLinearGroup.elementary i j hij a *
      (diagonalUnit F w)⁻¹ =
      _root_.Matrix.GeneralLinearGroup.elementary i j hij (((w i * (w j)⁻¹ : Fˣ) : F) * a) := by
  apply Units.ext
  change Matrix.diagonal (fun t => (w t : F)) * (1 + Matrix.single i j a) *
    Matrix.diagonal (fun t => (((w t)⁻¹ : Fˣ) : F)) = _
  ext r s
  by_cases hrs : r = s <;> by_cases hir : i = r <;> by_cases hjs : j = s <;>
    simp_all [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.GeneralLinearGroup.elementary,
      mul_assoc, mul_comm]

/-- Weight `q` on `s`, balanced at `h` by the inverse of `q ^ s.card`. -/
def balancedWeights {n : ℕ} (q : Fˣ) (s : Finset (Fin n)) (h : Fin n) : Fin n → Fˣ :=
  fun k => (if k ∈ s then q else 1) * (Pi.mulSingle h (q ^ s.card)⁻¹ : Fin n → Fˣ) k

lemma balancedWeights_prod {n : ℕ} (q : Fˣ) (s : Finset (Fin n)) (h : Fin n) :
    ∏ k, balancedWeights F q s h k = 1 := by
  simp only [balancedWeights, Finset.prod_mul_distrib]
  rw [Finset.prod_ite_mem_eq]
  simp

lemma balancedWeights_apply {n : ℕ} (q : Fˣ) (s : Finset (Fin n)) (h k : Fin n)
    (hkh : k ≠ h) : balancedWeights F q s h k = if k ∈ s then q else 1 := by
  simp [balancedWeights, hkh]

/-- A fresh balancing coordinate exists even when some of the four indices coincide. -/
lemma exists_fresh_four {n : ℕ} (hn : 5 ≤ n) (i j k l : Fin n) :
    ∃ h : Fin n, h ≠ i ∧ h ≠ j ∧ h ≠ k ∧ h ≠ l := by
  let s : Finset (Fin n) := {i, j, k, l}
  have hs : s.card ≤ 4 := by
    have h1 := Finset.card_insert_le i ({j, k, l} : Finset (Fin n))
    have h2 := Finset.card_insert_le j ({k, l} : Finset (Fin n))
    have h3 := Finset.card_insert_le k ({l} : Finset (Fin n))
    have h4 := Finset.card_singleton l
    dsimp [s]
    omega
  have hlt : s.card < (Finset.univ : Finset (Fin n)).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨h, _, hh⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  exact ⟨h, by simpa only [s, Finset.mem_insert, Finset.mem_singleton, not_or] using hh⟩

/-- Every nonidentical disjoint root pair has an actual balanced diagonal scaling
its first root by `q` and fixing its second. Identical roots are additive. -/
theorem exists_disjoint_weights {n : ℕ} (hn : 5 ≤ n) (q : Fˣ)
    (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i) (hne : ¬(i = k ∧ j = l)) :
    ∃ w : Fin n → Fˣ, (∏ t, w t = 1) ∧
      w i * (w j)⁻¹ = q ∧ w k * (w l)⁻¹ = 1 := by
  obtain ⟨h, hhi, hhj, hhk, hhl⟩ := exists_fresh_four hn i j k l
  by_cases hik : i = k
  · subst k
    have hjl : j ≠ l := by simpa using hne
    refine ⟨balancedWeights F q {i, l} h, balancedWeights_prod F q {i, l} h, ?_, ?_⟩
    · simp [balancedWeights_apply F q {i, l} h i hhi.symm,
        balancedWeights_apply F q {i, l} h j hhj.symm, hij.symm, hjl]
    · simp [balancedWeights_apply F q {i, l} h i hhi.symm,
        balancedWeights_apply F q {i, l} h l hhl.symm]
  · refine ⟨balancedWeights F q {i} h, balancedWeights_prod F q {i} h, ?_, ?_⟩
    · simp [balancedWeights_apply F q {i} h i hhi.symm,
        balancedWeights_apply F q {i} h j hhj.symm, hij.symm]
    · simp [balancedWeights_apply F q {i} h k hhk.symm,
        balancedWeights_apply F q {i} h l hhl.symm, Ne.symm hik, hli]

/-- One balanced diagonal doubles both the first and output roots of a chain. -/
theorem exists_chain_weights {n : ℕ} (hn : 5 ≤ n) (q : Fˣ)
    (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) :
    ∃ w : Fin n → Fˣ, (∏ t, w t = 1) ∧
      w i * (w j)⁻¹ = q ∧ w j * (w k)⁻¹ = 1 ∧ w i * (w k)⁻¹ = q := by
  obtain ⟨h, hhi, hhj, hhk, _⟩ := exists_fresh_four hn i j k k
  refine ⟨balancedWeights F q {i} h, balancedWeights_prod F q {i} h, ?_, ?_, ?_⟩
  · simp [balancedWeights_apply F q {i} h i hhi.symm,
      balancedWeights_apply F q {i} h j hhj.symm, hij.symm]
  · simp [balancedWeights_apply F q {i} h j hhj.symm,
      balancedWeights_apply F q {i} h k hhk.symm, hij.symm, hik.symm]
  · simp [balancedWeights_apply F q {i} h i hhi.symm,
      balancedWeights_apply F q {i} h k hhk.symm, hik.symm]

section Two
variable [CharZero F]

/-- The only field-specific unit used by the doubling proof. -/
def twoUnit : Fˣ := Units.mk0 (2 : F) two_ne_zero

@[simp] lemma twoUnit_val : ((twoUnit F : Fˣ) : F) = 2 := rfl

end Two

variable {F} {G : Type v} [Group G] {n : ℕ}

/-- Additive root sections, evaluated with the literal field coefficient. -/
def root (R : (i j : Fin n) → i ≠ j → Multiplicative F →* G)
    (i j : Fin n) (hij : i ≠ j) (a : F) : G := R i j hij (Multiplicative.ofAdd a)

lemma root_add (R : (i j : Fin n) → i ≠ j → Multiplicative F →* G)
    (i j : Fin n) (hij : i ≠ j) (a b : F) :
    root R i j hij (a + b) = root R i j hij a * root R i j hij b :=
  map_mul (R i j hij) (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)

lemma root_double (R : (i j : Fin n) → i ≠ j → Multiplicative F →* G)
    (i j : Fin n) (hij : i ≠ j) (a : F) :
    root R i j hij ((2 : F) * a) = root R i j hij a ^ 2 := by
  rw [two_mul, root_add, pow_two]

/-- Covariance is about lifts of literal product-one diagonal matrices.
This input states neither a Steinberg relation nor an ordered defect formula. -/
def DiagonalCovariance (p : G →* Matrix.GeneralLinearGroup (Fin n) F)
    (R : (i j : Fin n) → i ≠ j → Multiplicative F →* G) : Prop :=
  ∀ w : Fin n → Fˣ, (∏ t, w t = 1) →
    ∃ d : G, p d = diagonalUnit F w ∧
      ∀ (i j : Fin n) (hij : i ≠ j) (a : F),
        d * root R i j hij a * d⁻¹ =
          root R i j hij (((w i * (w j)⁻¹ : Fˣ) : F) * a)

variable [CharZero F]

/-- All original disjoint-root cases, including shared row and shared column. -/
theorem root_commute
    (p : G →* Matrix.GeneralLinearGroup (Fin n) F) (hc : p.ker ≤ Subgroup.center G)
    (R : (i j : Fin n) → i ≠ j → Multiplicative F →* G)
    (hR : ∀ (i j : Fin n) (hij : i ≠ j) (a : F),
      p (root R i j hij a) = _root_.Matrix.GeneralLinearGroup.elementary i j hij a)
    (hD : DiagonalCovariance p R) (hn : 5 ≤ n)
    (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i) (a b : F) :
    Commute (root R i j hij a) (root R k l hkl b) := by
  by_cases he : i = k ∧ j = l
  · obtain ⟨rfl, rfl⟩ := he
    change root R i j hij a * root R i j hij b = root R i j hij b * root R i j hij a
    rw [← root_add, ← root_add, add_comm]
  · obtain ⟨w, hw, hwij, hwkl⟩ := exists_disjoint_weights F hn (twoUnit F)
      i j k l hij hkl hjk hli he
    obtain ⟨d, _, hd⟩ := hD w hw
    apply _root_.MonoidHom.CentralKernel.Doubling.commute_of_central_ker_of_conj_square p hc
    · rw [hR, hR]
      exact _root_.Matrix.GeneralLinearGroup.elementary_commute i j k l hij hkl hjk hli a b
    · simpa only [hwij, twoUnit_val, root_double] using hd i j hij a
    · simpa only [hwkl, Units.val_one, one_mul] using hd k l hkl b

/-- The original ordered chain relation, with coefficient exactly `a * b`. -/
theorem root_commutator
    (p : G →* Matrix.GeneralLinearGroup (Fin n) F) (hc : p.ker ≤ Subgroup.center G)
    (R : (i j : Fin n) → i ≠ j → Multiplicative F →* G)
    (hR : ∀ (i j : Fin n) (hij : i ≠ j) (a : F),
      p (root R i j hij a) = _root_.Matrix.GeneralLinearGroup.elementary i j hij a)
    (hD : DiagonalCovariance p R) (hn : 5 ≤ n)
    (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : F) :
    ⁅root R i j hij a, root R j k hjk b⁆ = root R i k hik (a * b) := by
  obtain ⟨w, hw, hwij, hwjk, hwik⟩ := exists_chain_weights F hn (twoUnit F) i j k hij hik
  obtain ⟨d, _, hd⟩ := hD w hw
  apply _root_.MonoidHom.CentralKernel.Doubling.chain_of_central_ker_of_conj_square p hc
  · rw [map_commutatorElement, hR, hR, hR]
    exact _root_.Matrix.GeneralLinearGroup.elementary_commutator i j k hij hjk hik a b
  · exact root_commute p hc R hR hD hn i j i k hij hik hij.symm hik.symm a (a * b)
  · simpa only [hwij, twoUnit_val, root_double] using hd i j hij a
  · simpa only [hwjk, Units.val_one, one_mul] using hd j k hjk b
  · simpa only [hwik, twoUnit_val, root_double] using hd i k hik (a * b)

/-- Conditional finite-rank realization of all three original root laws. -/
theorem original_root_relations
    (p : G →* Matrix.GeneralLinearGroup (Fin n) F) (hc : p.ker ≤ Subgroup.center G)
    (R : (i j : Fin n) → i ≠ j → Multiplicative F →* G)
    (hR : ∀ (i j : Fin n) (hij : i ≠ j) (a : F),
      p (root R i j hij a) = _root_.Matrix.GeneralLinearGroup.elementary i j hij a)
    (hD : DiagonalCovariance p R) (hn : 5 ≤ n) :
    (∀ (i j : Fin n) (hij : i ≠ j) (a b : F),
      root R i j hij a * root R i j hij b = root R i j hij (a + b)) ∧
    (∀ (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
        (_hjk : j ≠ k) (_hli : l ≠ i) (a b : F),
      ⁅root R i j hij a, root R k l hkl b⁆ = 1) ∧
    (∀ (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : F),
      ⁅root R i j hij a, root R j k hjk b⁆ = root R i k hik (a * b)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij a b
    exact (root_add R i j hij a b).symm
  · intro i j k l hij hkl hjk hli a b
    exact (root_commute p hc R hR hD hn i j k l hij hkl hjk hli a b).commutator_eq
  · exact root_commutator p hc R hR hD hn

end StableSteinberg.FiniteRootLifting

end

end
