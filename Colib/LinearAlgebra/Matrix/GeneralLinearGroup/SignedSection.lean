/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, kangxyz
-/
module

public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Data.Finset.Card
public import Colib.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Basic

Adapted from Quillen Aglib/LinearAlgebra/Matrix/GeneralLinearGroup/SignedSection/Basic.lean at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using native matrix units and Milnor coefficients.

The declarations retain their original field, rank, central-kernel and explicit
transport hypotheses. Their current consumer is the finite Matsumoto normalizer,
Bruhat action, or conditional original-root detector construction.

-/

@[expose] public section

/-! ## SignedSectionCounts -/

section

/-!
# Prefix inversion counts under a native adjacent value swap

Multiplication of permutations follows the native convention: `(s * σ) j = s (σ j)`.
The two affected columns are compared by their original inverse positions.
-/
namespace Matrix.GeneralLinearGroup.SignedSection

/-- The actual native adjacent permutation. -/
def adjacentSwap {n : ℕ} (i : Fin n) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.swap i.castSucc i.succ

@[simp] lemma adjacentSwap_lower {n : ℕ} (i : Fin n) :
    adjacentSwap i i.castSucc = i.succ := Equiv.swap_apply_left _ _

@[simp] lemma adjacentSwap_upper {n : ℕ} (i : Fin n) :
    adjacentSwap i i.succ = i.castSucc := Equiv.swap_apply_right _ _

lemma adjacent_lower_lt_upper {n : ℕ} (i : Fin n) : i.castSucc < i.succ := by
  simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
  omega

lemma adjacentSwap_above_upper {n : ℕ} (i : Fin n) (x : Fin (n + 1)) :
    i.succ < adjacentSwap i x ↔ i.castSucc < x ∧ x ≠ i.succ := by
  by_cases hxa : x = i.castSucc
  · subst x
    simp
  by_cases hxb : x = i.succ
  · subst x
    simp [not_lt_of_ge (adjacent_lower_lt_upper i).le]
  rw [show adjacentSwap i x = x from Equiv.swap_apply_of_ne_of_ne hxa hxb]
  have hval : x.val ≠ i.val + 1 := by
    intro h
    apply hxb
    apply Fin.ext
    simpa only [Fin.val_succ] using h
  simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
  omega

lemma adjacentSwap_above_lower {n : ℕ} (i : Fin n) (x : Fin (n + 1)) :
    i.castSucc < adjacentSwap i x ↔ i.succ < x ∨ x = i.castSucc := by
  by_cases hxa : x = i.castSucc
  · subst x
    simp
  by_cases hxb : x = i.succ
  · subst x
    simp [hxa]
  rw [show adjacentSwap i x = x from Equiv.swap_apply_of_ne_of_ne hxa hxb]
  have hval : x.val ≠ i.val + 1 := by
    intro h
    apply hxb
    apply Fin.ext
    simpa only [Fin.val_succ] using h
  simp only [hxa, or_false, Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
  omega

lemma adjacentSwap_order_away {n : ℕ} (i : Fin n) (x y : Fin (n + 1))
    (hya : y ≠ i.castSucc) (hyb : y ≠ i.succ) :
    adjacentSwap i y < adjacentSwap i x ↔ y < x := by
  rw [show adjacentSwap i y = y from Equiv.swap_apply_of_ne_of_ne hya hyb]
  have hva : y.val ≠ i.val := by
    intro h
    exact hya (Fin.ext (by simpa only [Fin.val_castSucc] using h))
  have hvb : y.val ≠ i.val + 1 := by
    intro h
    exact hyb (Fin.ext (by simpa only [Fin.val_succ] using h))
  by_cases hxa : x = i.castSucc
  · subst x
    rw [adjacentSwap_lower]
    simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
    omega
  by_cases hxb : x = i.succ
  · subst x
    rw [adjacentSwap_upper]
    simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
    omega
  rw [show adjacentSwap i x = x from Equiv.swap_apply_of_ne_of_ne hxa hxb]

/-- Earlier columns whose image exceeds the image of the selected column. -/
def prefixSet {m : ℕ} (σ : Equiv.Perm (Fin m)) (j : Fin m) : Finset (Fin m) :=
  Finset.univ.filter (fun k => k < j ∧ σ j < σ k)

lemma mem_prefixSet {m : ℕ} (σ : Equiv.Perm (Fin m)) (j k : Fin m) :
    k ∈ prefixSet σ j ↔ k < j ∧ σ j < σ k := by
  simp only [prefixSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The exact prefix inversion count in the requested signed section. -/
def prefixCount {m : ℕ} (σ : Equiv.Perm (Fin m)) (j : Fin m) : ℕ :=
  (prefixSet σ j).card

@[simp] lemma prefixCount_one {m : ℕ} (j : Fin m) : prefixCount (1 : Equiv.Perm (Fin m)) j = 0 := by
  have he : prefixSet (1 : Equiv.Perm (Fin m)) j = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro k _ hk
    exact lt_asymm hk.1 hk.2
  simp only [prefixCount, he, Finset.card_empty]

/-- At the lower-valued column, the larger adjacent value is the only erased inversion. -/
lemma prefixCount_lower {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n)
    (j : Fin (n + 1)) (hj : σ j = i.castSucc) :
    prefixCount σ j = prefixCount (adjacentSwap i * σ) j +
      if σ⁻¹ i.succ < j then 1 else 0 := by
  have he : prefixSet (adjacentSwap i * σ) j = (prefixSet σ j).erase (σ⁻¹ i.succ) := by
    ext k
    simp only [prefixSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
      Equiv.Perm.mul_apply, hj, adjacentSwap_lower, adjacentSwap_above_upper]
    have heq : σ k = i.succ ↔ k = σ⁻¹ i.succ := by
      constructor
      · intro h
        simpa using congrArg σ.symm h
      · intro h
        simp [h]
    constructor
    · rintro ⟨hkj, hσ, hne⟩
      exact ⟨(fun h => hne (heq.mpr h)), hkj, hσ⟩
    · rintro ⟨hne, hkj, hσ⟩
      exact ⟨hkj, hσ, (fun h => hne (heq.mp h))⟩
  have hmem : σ⁻¹ i.succ ∈ prefixSet σ j ↔ σ⁻¹ i.succ < j := by
    simp [prefixSet, hj]
  unfold prefixCount
  rw [he]
  by_cases hp : σ⁻¹ i.succ < j
  · rw [ite_eq_left hp]
    exact (Finset.card_erase_add_one (hmem.mpr hp)).symm
  · simp only [ite_eq_right hp, Nat.add_zero,
      Finset.erase_eq_of_notMem (show σ⁻¹ i.succ ∉ prefixSet σ j from fun h => hp (hmem.mp h))]

/-- At the upper-valued column, exactly the earlier lower value is newly counted. -/
lemma prefixCount_upper {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n)
    (j : Fin (n + 1)) (hj : σ j = i.succ) :
    prefixCount (adjacentSwap i * σ) j = prefixCount σ j +
      if σ⁻¹ i.castSucc < j then 1 else 0 := by
  have hj' : (adjacentSwap i * σ) j = i.castSucc := by
    simp only [Equiv.Perm.mul_apply, hj, adjacentSwap_upper]
  have hh := prefixCount_lower (adjacentSwap i * σ) i j hj'
  have hinv : (adjacentSwap i * σ)⁻¹ i.succ = σ⁻¹ i.castSucc := by
    simp [_root_.mul_inv_rev, adjacentSwap, Equiv.Perm.mul_apply]
  have hsq : adjacentSwap i * (adjacentSwap i * σ) = σ := by
    rw [← mul_assoc, show adjacentSwap i * adjacentSwap i = 1 from Equiv.swap_mul_self _ _,
      one_mul]
  simpa only [hsq, hinv] using hh

/-- Every other column has exactly the same prefix inversion set cardinality. -/
lemma prefixCount_away {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n)
    (j : Fin (n + 1)) (hja : σ j ≠ i.castSucc) (hjb : σ j ≠ i.succ) :
    prefixCount (adjacentSwap i * σ) j = prefixCount σ j := by
  have he : prefixSet (adjacentSwap i * σ) j = prefixSet σ j := by
    ext k
    rw [mem_prefixSet, mem_prefixSet]
    change (k < j ∧ adjacentSwap i (σ j) < adjacentSwap i (σ k)) ↔ k < j ∧ σ j < σ k
    rw [adjacentSwap_order_away i (σ k) (σ j) hja hjb]
  exact congrArg Finset.card he

end Matrix.GeneralLinearGroup.SignedSection

end

/-! ## SignedSection -/

section

/-!
# The actual signed permutation matrix section

Column `j` is `(-1)^(prefixCount σ j)` times the basis vector at `σ j`.
The unit has an explicit inverse. Native `permMatrix` conventions are not used.
-/
noncomputable section

universe u

namespace Matrix.GeneralLinearGroup.SignedSection

variable (F : Type u) [Field F]

/-- The column-monomial matrix with the specified native permutation and unit coefficients. -/
def columnMatrix {m : ℕ} (σ : Equiv.Perm (Fin m)) (d : Fin m → Fˣ) :
    Matrix (Fin m) (Fin m) F := fun r j => if r = σ j then (d j : F) else 0

/-- The exact inverse matrix, written without any permutation-matrix convention. -/
def columnInverse {m : ℕ} (σ : Equiv.Perm (Fin m)) (d : Fin m → Fˣ) :
    Matrix (Fin m) (Fin m) F := fun r j => if σ r = j then ((d r)⁻¹ : Fˣ) else 0

/-- The actual finite GL element with the displayed column formula and explicit inverse. -/
def columnUnit {m : ℕ} (σ : Equiv.Perm (Fin m)) (d : Fin m → Fˣ) :
    Matrix.GeneralLinearGroup (Fin m) F where
  val := columnMatrix F σ d
  inv := columnInverse F σ d
  val_inv := by
    ext r j
    rw [Matrix.mul_apply, Finset.sum_eq_single (σ⁻¹ r)]
    · simp [columnMatrix, columnInverse, Matrix.one_apply]
    · intro k _ hk
      have hne : r ≠ σ k := by
        intro h
        apply hk
        simpa using (congrArg σ.symm h).symm
      simp [columnMatrix, hne]
    · simp
  inv_val := by
    ext r j
    rw [Matrix.mul_apply, Finset.sum_eq_single (σ j)]
    · by_cases h : r = j
      · subst j
        simp [columnMatrix, columnInverse]
      · simp [columnMatrix, columnInverse, h, σ.injective.ne h]
    · intro k _ hk
      simp [columnMatrix, hk]
    · simp

@[simp] lemma columnUnit_entry {m : ℕ} (σ : Equiv.Perm (Fin m)) (d : Fin m → Fˣ)
    (r j : Fin m) : (columnUnit F σ d).val r j = if r = σ j then (d j : F) else 0 := rfl

/-- The signed section with exactly the requested prefix inversion signs. -/
def sectionGL {m : ℕ} (σ : Equiv.Perm (Fin m)) : Matrix.GeneralLinearGroup (Fin m) F :=
  columnUnit F σ (fun j => (-1 : Fˣ) ^ prefixCount σ j)

lemma sectionGL_entry {m : ℕ} (σ : Equiv.Perm (Fin m)) (r j : Fin m) :
    (sectionGL F σ).val r j = if r = σ j then (-1 : F) ^ prefixCount σ j else 0 := by
  simp [sectionGL]

@[simp] lemma sectionGL_one (m : ℕ) : sectionGL F (1 : Equiv.Perm (Fin m)) = 1 := by
  apply Units.ext
  ext r j
  simp [sectionGL_entry, Matrix.one_apply]

lemma sectionGL_nonzero_iff {m : ℕ} (σ : Equiv.Perm (Fin m)) (r j : Fin m) :
    (sectionGL F σ).val r j ≠ 0 ↔ r = σ j := by
  rw [sectionGL_entry]
  by_cases h : r = σ j <;> simp [h]

/-- The column supports determine exactly the original native permutation. -/
theorem sectionGL_permutation_unique {m : ℕ} (σ ρ : Equiv.Perm (Fin m)) :
    (∀ j, (sectionGL F σ).val (ρ j) j ≠ 0) ↔ ρ = σ := by
  constructor
  · intro h
    apply Equiv.ext
    intro j
    exact (sectionGL_nonzero_iff F σ (ρ j) j).mp (h j)
  · intro h j
    rw [h]
    exact (sectionGL_nonzero_iff F σ (σ j) j).mpr rfl

theorem sectionGL_injective (m : ℕ) : Function.Injective (sectionGL F (m := m)) := by
  intro σ ρ h
  apply (sectionGL_permutation_unique F ρ σ).mp
  intro j
  rw [← h]
  exact (sectionGL_nonzero_iff F σ (σ j) j).mpr rfl

/-- The literal adjacent word `W_i(-1)` in the original elementary matrices. -/
def Wminus {n : ℕ} (i : Fin n) : Matrix.GeneralLinearGroup (Fin (n + 1)) F :=
  Matrix.GeneralLinearGroup.elementary i.castSucc i.succ i.castSucc_lt_succ.ne (-1) *
    Matrix.GeneralLinearGroup.elementary i.succ i.castSucc i.castSucc_lt_succ.ne.symm 1 *
    Matrix.GeneralLinearGroup.elementary i.castSucc i.succ i.castSucc_lt_succ.ne (-1)

/-- The actual diagonal with `-1` at the two adjacent positions. -/
def E {n : ℕ} (i : Fin n) : Matrix.GeneralLinearGroup (Fin (n + 1)) F :=
  columnUnit F 1 (fun r => if r = i.castSucc ∨ r = i.succ then -1 else 1)

lemma E_entry {n : ℕ} (i : Fin n) (r j : Fin (n + 1)) :
    (E F i).val r j =
      if r = j then (if r = i.castSucc ∨ r = i.succ then (-1 : F) else 1) else 0 := by
  by_cases h : r = j
  · subst j
    by_cases hr : r = i.castSucc ∨ r = i.succ <;> simp [E, hr]
  · simp [E, h]

/-- Actual elementary left multiplication, shared with the fixed matrix supplier. -/
lemma elementary_left_mul_entry {m : ℕ} (g : Matrix.GeneralLinearGroup (Fin m) F)
    (i j : Fin m) (hij : i ≠ j) (a : F) (r s : Fin m) :
    (Matrix.GeneralLinearGroup.elementary i j hij a * g).val r s =
      g.val r s + if r = i then a * g.val j s else 0 := by
  change ((1 + Matrix.single i j a) * g.val) r s = _
  rw [add_mul, one_mul, Matrix.add_apply]
  by_cases hr : r = i
  · subst r
    simp
  · rw [Matrix.single_mul_apply_of_ne a i j r s hr, ite_eq_right hr, add_zero]

lemma Wminus_mul_entry {n : ℕ} (i : Fin n)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) (r j : Fin (n + 1)) :
    (Wminus F i * g).val r j =
      if r = i.castSucc then -g.val i.succ j else
      if r = i.succ then g.val i.castSucc j else g.val r j := by
  have hij : i.castSucc ≠ i.succ := i.castSucc_lt_succ.ne
  simp only [Wminus, mul_assoc, elementary_left_mul_entry]
  by_cases hra : r = i.castSucc <;> by_cases hrb : r = i.succ <;>
    simp [hra, hrb, hij, hij.symm]

lemma E_mul_entry {n : ℕ} (i : Fin n)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) (r j : Fin (n + 1)) :
    (E F i * g).val r j =
      (if r = i.castSucc ∨ r = i.succ then (-1 : F) else 1) * g.val r j := by
  simp only [Units.val_mul, Matrix.mul_apply, E_entry]
  simp [ite_mul]

end Matrix.GeneralLinearGroup.SignedSection

end

end

/-! ## SignedSectionRecurrence -/

section

/-!
# Exact ascent and descent recurrence for the signed matrix section

The recurrence is an equality of actual finite matrix units. Its signs follow
from the proved change of the two affected prefix inversion counts.
-/
noncomputable section

universe u

namespace Matrix.GeneralLinearGroup.SignedSection

variable (F : Type u) [Field F]

lemma coefficient_lower {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n)
    (j : Fin (n + 1)) (hj : σ j = i.castSucc) :
    (-1 : F) ^ prefixCount σ j =
      if σ.symm i.succ < j then -((-1 : F) ^ prefixCount (adjacentSwap i * σ) j)
      else (-1 : F) ^ prefixCount (adjacentSwap i * σ) j := by
  rw [prefixCount_lower σ i j hj]
  by_cases hp : σ.symm i.succ < j <;> simp [hp, pow_succ]

lemma coefficient_upper {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n)
    (j : Fin (n + 1)) (hj : σ j = i.succ) :
    (-1 : F) ^ prefixCount (adjacentSwap i * σ) j =
      if σ.symm i.castSucc < j then -((-1 : F) ^ prefixCount σ j)
      else (-1 : F) ^ prefixCount σ j := by
  rw [prefixCount_upper σ i j hj]
  by_cases hp : σ.symm i.castSucc < j <;> simp [hp, pow_succ]

/-- An inverse-position ascent has exactly the uncorrected original matrix recurrence. -/
theorem Wminus_section_ascent {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n)
    (hpos : σ.symm i.castSucc < σ.symm i.succ) :
    Wminus F i * sectionGL F σ = sectionGL F (adjacentSwap i * σ) := by
  have hij : i.castSucc ≠ i.succ := i.castSucc_lt_succ.ne
  apply Units.ext
  ext r j
  by_cases hja : σ j = i.castSucc
  · have hjp : j = σ.symm i.castSucc := by simpa using congrArg σ.symm hja
    have hnot : ¬ σ.symm i.succ < j := by rw [hjp]; exact not_lt.mpr hpos.le
    have hc := coefficient_lower F σ i j hja
    simp only [ite_eq_right hnot] at hc
    simp only [Wminus_mul_entry, sectionGL_entry, Equiv.Perm.mul_apply]
    by_cases hra : r = i.castSucc <;> by_cases hrb : r = i.succ <;>
      simp [hra, hrb, hja, hij, hij.symm, hc]
  by_cases hjb : σ j = i.succ
  · have hjp : j = σ.symm i.succ := by simpa using congrArg σ.symm hjb
    have hlt : σ.symm i.castSucc < j := by rw [hjp]; exact hpos
    have hc := coefficient_upper F σ i j hjb
    simp only [ite_eq_left hlt] at hc
    simp only [Wminus_mul_entry, sectionGL_entry, Equiv.Perm.mul_apply]
    by_cases hra : r = i.castSucc <;> by_cases hrb : r = i.succ <;>
      simp [hra, hrb, hjb, hij, hij.symm, hc]
  · have hc : (-1 : F) ^ prefixCount (adjacentSwap i * σ) j =
        (-1 : F) ^ prefixCount σ j := by rw [prefixCount_away σ i j hja hjb]
    have hcomp : adjacentSwap i (σ j) = σ j :=
      Equiv.swap_apply_of_ne_of_ne hja hjb
    simp only [Wminus_mul_entry, sectionGL_entry, Equiv.Perm.mul_apply]
    by_cases hra : r = i.castSucc <;> by_cases hrb : r = i.succ <;>
      simp [hra, hrb, Ne.symm hja, Ne.symm hjb, hcomp, hc, hij.symm]

/-- An inverse-position descent has exactly the original two-row diagonal correction. -/
theorem Wminus_section_descent {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n)
    (hpos : σ.symm i.succ < σ.symm i.castSucc) :
    Wminus F i * sectionGL F σ = E F i * sectionGL F (adjacentSwap i * σ) := by
  have hij : i.castSucc ≠ i.succ := i.castSucc_lt_succ.ne
  apply Units.ext
  ext r j
  by_cases hja : σ j = i.castSucc
  · have hjp : j = σ.symm i.castSucc := by simpa using congrArg σ.symm hja
    have hlt : σ.symm i.succ < j := by rw [hjp]; exact hpos
    have hc := coefficient_lower F σ i j hja
    simp only [ite_eq_left hlt] at hc
    simp only [Wminus_mul_entry, E_mul_entry, sectionGL_entry, Equiv.Perm.mul_apply]
    by_cases hra : r = i.castSucc <;> by_cases hrb : r = i.succ <;>
      simp [hra, hrb, hja, hij, hij.symm, hc]
  by_cases hjb : σ j = i.succ
  · have hjp : j = σ.symm i.succ := by simpa using congrArg σ.symm hjb
    have hnot : ¬ σ.symm i.castSucc < j := by rw [hjp]; exact not_lt.mpr hpos.le
    have hc := coefficient_upper F σ i j hjb
    simp only [ite_eq_right hnot] at hc
    simp only [Wminus_mul_entry, E_mul_entry, sectionGL_entry, Equiv.Perm.mul_apply]
    by_cases hra : r = i.castSucc <;> by_cases hrb : r = i.succ <;>
      simp [hra, hrb, hjb, hij, hij.symm, hc]
  · have hc : (-1 : F) ^ prefixCount (adjacentSwap i * σ) j =
        (-1 : F) ^ prefixCount σ j := by rw [prefixCount_away σ i j hja hjb]
    have hcomp : adjacentSwap i (σ j) = σ j :=
      Equiv.swap_apply_of_ne_of_ne hja hjb
    simp only [Wminus_mul_entry, E_mul_entry, sectionGL_entry, Equiv.Perm.mul_apply]
    by_cases hra : r = i.castSucc <;> by_cases hrb : r = i.succ <;>
      simp [hra, hrb, Ne.symm hja, Ne.symm hjb, hcomp, hc, hij, hij.symm]

/-- The two native inverse-position cases exhaust the exact signed recurrence. -/
theorem Wminus_section {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin n) :
    Wminus F i * sectionGL F σ =
      if σ.symm i.castSucc < σ.symm i.succ then sectionGL F (adjacentSwap i * σ)
      else E F i * sectionGL F (adjacentSwap i * σ) := by
  by_cases hpos : σ.symm i.castSucc < σ.symm i.succ
  · rw [ite_eq_left hpos]
    exact Wminus_section_ascent F σ i hpos
  · rw [ite_eq_right hpos]
    have hne : σ.symm i.castSucc ≠ σ.symm i.succ :=
      σ.symm.injective.ne i.castSucc_lt_succ.ne
    exact Wminus_section_descent F σ i
      (lt_of_le_of_ne (le_of_not_gt hpos) (Ne.symm hne))

/-- The section on each adjacent permutation is literally the required `W_i(-1)` word. -/
@[simp] lemma sectionGL_adjacentSwap {n : ℕ} (i : Fin n) :
    sectionGL F (adjacentSwap i) = Wminus F i := by
  have hh := Wminus_section_ascent F (1 : Equiv.Perm (Fin (n + 1))) i
    (by change i.castSucc < i.succ; exact i.castSucc_lt_succ)
  simpa using hh.symm

/-- The displayed column formula is exactly the claimed action on each basis vector. -/
lemma sectionGL_mulVec_single {m : ℕ} (σ : Equiv.Perm (Fin m)) (j : Fin m) :
    Matrix.mulVec (sectionGL F σ).val (Pi.single j 1) =
      Pi.single (σ j) ((-1 : F) ^ prefixCount σ j) := by
  ext r
  simp [sectionGL_entry, Pi.single_apply]

end Matrix.GeneralLinearGroup.SignedSection

end

end
