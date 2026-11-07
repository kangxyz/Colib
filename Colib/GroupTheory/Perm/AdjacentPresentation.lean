/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, kangxyz
-/
module

public import Mathlib.Algebra.Group.Commute.Basic
public import Mathlib.Tactic.Group
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Algebra.Group.Submonoid.Membership

/-!
# Presentation

The adjacent generators of the native finite permutation group satisfy the
type-A presentation. The proof uses bounded bubble words and Mathlib
`PresentedGroup`, without a second permutation model.

Adapted from Quillen adjacent-permutation Presentation.lean at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section

/-! ## TypeABubble -/

section

/-!
# Bounded type-A bubble words

The descending word `bubble s n j = s(n-1) ... s(j)` is a finite coset
representative. Its right multiplication formulas use only the square,
distant commutation, and adjacent braid relations within the bound `n`.
-/
namespace Equiv.Perm.AdjacentPresentation

variable {G : Type*} [Group G] (s : ℕ → G)

/-- The descending adjacent-generator word, truncated at both natural bounds. -/
def bubble : ℕ → ℕ → G
  | 0, _ => 1
  | n + 1, j => if j ≤ n then s n * bubble n j else 1

@[simp] lemma bubble_zero (j : ℕ) : bubble s 0 j = 1 := rfl

lemma bubble_succ (n j : ℕ) (hj : j ≤ n) :
    bubble s (n + 1) j = s n * bubble s n j := by
  simp [bubble, hj]

lemma bubble_eq_one (n j : ℕ) (hn : n ≤ j) : bubble s n j = 1 := by
  cases n with
  | zero => rfl
  | succ n => simp [bubble, show ¬ j ≤ n by omega]

/-- A bubble word commutes with an element commuting with all letters in its interval. -/
lemma bubble_commute (n j : ℕ) (a : G)
    (hcomm : ∀ k, j ≤ k → k < n → Commute (s k) a) : Commute (bubble s n j) a := by
  induction n with
  | zero => simp
  | succ n ih =>
      by_cases hj : j ≤ n
      · rw [bubble_succ s n j hj]
        exact (hcomm n hj (by omega)).mul_left
          (ih (fun k hjk hkn => hcomm k hjk (by omega)))
      · simp [bubble, hj]

/-- Appending the immediately preceding letter extends the descending word. -/
lemma bubble_mul_pred (n : ℕ) : ∀ i, i < n →
    bubble s n (i + 1) * s i = bubble s n i := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
      intro i hi
      by_cases hin : i < n
      · rw [bubble_succ s n (i + 1) (by omega), bubble_succ s n i (by omega),
          mul_assoc, ih i hin]
      · have he : i = n := by omega
        subst i
        rw [bubble_eq_one s (n + 1) (n + 1) le_rfl,
          bubble_succ s n n le_rfl, bubble_eq_one s n n le_rfl]
        simp

/-- Appending the final letter cancels it by its square relation. -/
lemma bubble_mul_self (n i : ℕ) (hi : i < n) (hsq : s i * s i = 1) :
    bubble s n i * s i = bubble s n (i + 1) := by
  rw [← bubble_mul_pred s n i hi, mul_assoc, hsq, mul_one]

/-- Letters strictly below the bubble interval commute to its left. -/
lemma bubble_mul_low (n j i : ℕ) (hi : i < n) (hij : i + 1 < j)
    (hcomm : ∀ k l, k < n → l < n → k + 1 < l → Commute (s k) (s l)) :
    bubble s n j * s i = s i * bubble s n j := by
  exact (bubble_commute s n j (s i)
    (fun k hjk hk => (hcomm i k hi hk (by omega)).symm)).eq

/-- The upper right-multiplication case, obtained by one braid and distant commutations. -/
lemma bubble_mul_high (n : ℕ) : ∀ j i, j < i → i < n →
    (∀ k l, k < n → l < n → k + 1 < l → Commute (s k) (s l)) →
    (∀ k, k + 1 < n → s k * s (k + 1) * s k = s (k + 1) * s k * s (k + 1)) →
    bubble s n j * s i = s (i - 1) * bubble s n j := by
  induction n with
  | zero => intro j i hji hi; omega
  | succ n ih =>
      intro j i hji hi hcomm hbraid
      rw [bubble_succ s n j (by omega)]
      by_cases hin : i < n
      · have he := ih j i hji hin
          (fun k l hk hl hkl => hcomm k l (by omega) (by omega) hkl)
          (fun k hk => hbraid k (by omega))
        rw [mul_assoc, he, ← mul_assoc,
          (hcomm (i - 1) n (by omega) (by omega) (by omega)).symm.eq, mul_assoc]
      · have he : i = n := by omega
        subst i
        cases n with
        | zero => omega
        | succ m =>
            rw [bubble_succ s m j (by omega)]
            have hc : Commute (bubble s m j) (s (m + 1)) :=
              bubble_commute s m j (s (m + 1))
                (fun k _ hk => hcomm k (m + 1) (by omega) (by omega) (by omega))
            calc
              (s (m + 1) * (s m * bubble s m j)) * s (m + 1) =
                  (s (m + 1) * s m * s (m + 1)) * bubble s m j := by
                simpa only [mul_assoc] using
                  congrArg (fun z => s (m + 1) * (s m * z)) hc.eq
              _ = (s m * s (m + 1) * s m) * bubble s m j := by
                rw [(hbraid m (by omega)).symm]
              _ = s (m + 1 - 1) * (s (m + 1) * (s m * bubble s m j)) := by
                simp only [Nat.add_sub_cancel, mul_assoc]

end Equiv.Perm.AdjacentPresentation

end

/-! ## TypeAPresentation -/

section

/-!
# The adjacent-swap presentation of the actual finite symmetric group

The group on `Fin n` generators has exactly the square, ordered distant
commutation, and adjacent braid relators. Its marked map sends generator `i`
to the native permutation swapping `i.castSucc` and `i.succ`.
The proof of injectivity uses bounded descending bubble coset normal forms.
-/
noncomputable section

namespace Equiv.Perm.AdjacentPresentation

/-- The exact square, distant commutation, and adjacent braid relators. -/
inductive Relator (n : ℕ) : FreeGroup (Fin n) → Prop
  | square (i : Fin n) : Relator n (FreeGroup.of i * FreeGroup.of i)
  | distant (i j : Fin n) (hij : i.val + 1 < j.val) :
      Relator n ((FreeGroup.of i * FreeGroup.of j) *
        (FreeGroup.of j * FreeGroup.of i)⁻¹)
  | braid (i j : Fin n) (hij : i.val + 1 = j.val) :
      Relator n ((FreeGroup.of i * FreeGroup.of j * FreeGroup.of i) *
        (FreeGroup.of j * FreeGroup.of i * FreeGroup.of j)⁻¹)

/-- The actual defining set of words. -/
def relations (n : ℕ) : Set (FreeGroup (Fin n)) := {r | Relator n r}

/-- The explicit adjacent-swap presented group on `n` generators. -/
abbrev Group (n : ℕ) := PresentedGroup (relations n)

/-- Its marked finite generator. -/
def simple (n : ℕ) (i : Fin n) : Group n := PresentedGroup.of i

@[simp] lemma simple_square (n : ℕ) (i : Fin n) : simple n i * simple n i = 1 := by
  simpa only [simple, map_mul, PresentedGroup.of] using
    PresentedGroup.one_of_mem (rels := relations n) (Relator.square i)

lemma simple_commute (n : ℕ) (i j : Fin n) (hij : i.val + 1 < j.val) :
    Commute (simple n i) (simple n j) := by
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (Relator.distant i j hij)

lemma simple_braid (n : ℕ) (i j : Fin n) (hij : i.val + 1 = j.val) :
    simple n i * simple n j * simple n i = simple n j * simple n i * simple n j := by
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (Relator.braid i j hij)

/-- The finite generators extended by identity outside their natural bound. -/
def letter (n i : ℕ) : Group n := if hi : i < n then simple n ⟨i, hi⟩ else 1

lemma letter_of_lt (n i : ℕ) (hi : i < n) : letter n i = simple n ⟨i, hi⟩ := by
  simp [letter, hi]

@[simp] lemma letter_val (n : ℕ) (i : Fin n) : letter n i.val = simple n i := by
  simp [letter, i.isLt]

lemma letter_square (n i : ℕ) (hi : i < n) : letter n i * letter n i = 1 := by
  simp only [letter_of_lt n i hi, simple_square]

lemma letter_commute (n i j : ℕ) (hi : i < n) (hj : j < n) (hij : i + 1 < j) :
    Commute (letter n i) (letter n j) := by
  simpa only [letter_of_lt n i hi, letter_of_lt n j hj] using
    simple_commute n ⟨i, hi⟩ ⟨j, hj⟩ hij

lemma letter_braid (n i : ℕ) (hi : i + 1 < n) :
    letter n i * letter n (i + 1) * letter n i =
      letter n (i + 1) * letter n i * letter n (i + 1) := by
  simpa only [letter_of_lt n i (by omega), letter_of_lt n (i + 1) hi] using
    simple_braid n ⟨i, by omega⟩ ⟨i + 1, hi⟩ rfl

section Lift

variable {n : ℕ} {G : Type*} [_root_.Group G] (s : Fin n → G)
    (hsq : ∀ i, s i * s i = 1)
    (hcomm : ∀ i j, i.val + 1 < j.val → Commute (s i) (s j))
    (hbraid : ∀ i j, i.val + 1 = j.val → s i * s j * s i = s j * s i * s j)

include hsq hcomm hbraid

lemma lift_relations (r : FreeGroup (Fin n)) (hr : r ∈ relations n) :
    FreeGroup.lift s r = 1 := by
  cases hr with
  | square i => simpa only [map_mul, FreeGroup.lift_apply_of] using hsq i
  | distant i j hij =>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [(hcomm i j hij).eq]
      exact mul_inv_cancel _
  | braid i j hij =>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      rw [hbraid i j hij]
      exact mul_inv_cancel _

/-- The concrete universal homomorphism for the three listed relation families. -/
def lift : Group n →* G := PresentedGroup.toGroup (lift_relations s hsq hcomm hbraid)

@[simp] lemma lift_simple (i : Fin n) : lift s hsq hcomm hbraid (simple n i) = s i :=
  PresentedGroup.toGroup.of _

end Lift

/-- Standard inclusion of the first `n` generators into the next presented group. -/
def includePrev (n : ℕ) : Group n →* Group (n + 1) :=
  lift (fun i => simple (n + 1) i.castSucc)
    (fun i => simple_square (n + 1) i.castSucc)
    (fun i j hij => simple_commute (n + 1) i.castSucc j.castSucc hij)
    (fun i j hij => simple_braid (n + 1) i.castSucc j.castSucc hij)

@[simp] lemma includePrev_simple (n : ℕ) (i : Fin n) :
    includePrev n (simple n i) = simple (n + 1) i.castSucc := lift_simple _ _ _ _ i

lemma includePrev_letter (n i : ℕ) (hi : i < n) :
    includePrev n (letter n i) = letter (n + 1) i := by
  rw [letter_of_lt n i hi, includePrev_simple, letter_of_lt (n + 1) i (by omega)]
  rfl

/-- Native marked adjacent swaps in the original finite permutation group. -/
def adjacentSwap (n : ℕ) (i : Fin n) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.swap i.castSucc i.succ

@[simp] lemma adjacentSwap_square (n : ℕ) (i : Fin n) :
    adjacentSwap n i * adjacentSwap n i = 1 := Equiv.swap_mul_self _ _

lemma adjacentSwap_commute (n : ℕ) (i j : Fin n) (hij : i.val + 1 < j.val) :
    Commute (adjacentSwap n i) (adjacentSwap n j) := by
  change Equiv.swap i.castSucc i.succ * Equiv.swap j.castSucc j.succ =
    Equiv.swap j.castSucc j.succ * Equiv.swap i.castSucc i.succ
  rw [Equiv.mul_swap_eq_swap_mul]
  have hji : j.castSucc ≠ i.castSucc := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castSucc] at this
    omega
  have hji' : j.castSucc ≠ i.succ := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at this
    omega
  have hj'i : j.succ ≠ i.castSucc := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at this
    omega
  have hj'i' : j.succ ≠ i.succ := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_succ] at this
    omega
  rw [Equiv.swap_apply_of_ne_of_ne hji hji', Equiv.swap_apply_of_ne_of_ne hj'i hj'i']

lemma adjacentSwap_braid (n : ℕ) (i j : Fin n) (hij : i.val + 1 = j.val) :
    adjacentSwap n i * adjacentSwap n j * adjacentSwap n i =
      adjacentSwap n j * adjacentSwap n i * adjacentSwap n j := by
  have hb : i.succ = j.castSucc := Fin.ext hij
  have hca : j.succ ≠ i.castSucc := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at this
    omega
  have hcb : j.succ ≠ i.succ := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_succ] at this
    omega
  have hab : i.castSucc ≠ i.succ := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at this
    omega
  change Equiv.swap i.castSucc i.succ * Equiv.swap j.castSucc j.succ *
      Equiv.swap i.castSucc i.succ =
    Equiv.swap j.castSucc j.succ * Equiv.swap i.castSucc i.succ *
      Equiv.swap j.castSucc j.succ
  rw [← hb]
  calc
    _ = Equiv.swap i.castSucc j.succ := by
      simpa only [Equiv.swap_comm j.succ i.succ, Equiv.swap_comm i.succ i.castSucc] using
        Equiv.swap_mul_swap_mul_swap (x := j.succ) (y := i.succ) (z := i.castSucc) hcb hca
    _ = _ := by
      symm
      simpa only [Equiv.swap_comm j.succ i.castSucc] using
        Equiv.swap_mul_swap_mul_swap (x := i.castSucc) (y := i.succ) (z := j.succ)
          hab hca.symm

/-- The marked homomorphism into the original native symmetric group. -/
def toPerm (n : ℕ) : Group n →* Equiv.Perm (Fin (n + 1)) :=
  lift (adjacentSwap n) (adjacentSwap_square n) (adjacentSwap_commute n)
    (adjacentSwap_braid n)

@[simp] lemma toPerm_simple (n : ℕ) (i : Fin n) :
    toPerm n (simple n i) = Equiv.swap i.castSucc i.succ := lift_simple _ _ _ _ i

lemma toPerm_surjective (n : ℕ) : Function.Surjective (toPerm n) := by
  have hle : Submonoid.closure (Set.range (adjacentSwap n)) ≤
      (toPerm n).range.toSubmonoid := by
    apply Submonoid.closure_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨simple n i, toPerm_simple n i⟩
  have htop : Submonoid.closure (Set.range (adjacentSwap n)) = ⊤ :=
    Equiv.Perm.mclosure_swap_castSucc_succ n
  intro g
  exact hle (by rw [htop]; trivial)

@[simp] lemma simple_inv (n : ℕ) (i : Fin n) : (simple n i)⁻¹ = simple n i :=
  (eq_inv_of_mul_eq_one_right (simple_square n i)).symm

open _root_.Set in
open scoped Pointwise in
lemma simple_mclosure (n : ℕ) : Submonoid.closure (Set.range (simple n)) = ⊤ := by
  have hi : range (simple n) = range (simple n) ∪ (range (simple n))⁻¹ := by
    simp_rw [inv_range, simple_inv, union_self]
  have hg : Subgroup.closure (range (simple n)) = ⊤ :=
    PresentedGroup.closure_range_of (relations n)
  rw [hi, ← Subgroup.closure_toSubmonoid, hg, Subgroup.top_toSubmonoid]

/-- Each right multiplication of a bubble representative has a smaller-rank factor. -/
lemma bubble_mul_simple (n : ℕ) (j : Fin (n + 2)) (i : Fin (n + 1)) :
    ∃ v : Group n, ∃ k : Fin (n + 2),
      bubble (letter (n + 1)) (n + 1) j.val * simple (n + 1) i =
        includePrev n v * bubble (letter (n + 1)) (n + 1) k.val := by
  by_cases hlow : i.val + 1 < j.val
  · have hi : i.val < n := by have := j.isLt; omega
    refine ⟨simple n ⟨i.val, hi⟩, j, ?_⟩
    rw [← letter_val (n + 1) i]
    rw [bubble_mul_low (letter (n + 1)) (n + 1) j.val i.val i.isLt hlow
      (fun k l hk hl hkl => letter_commute (n + 1) k l hk hl hkl)]
    rw [includePrev_simple, ← letter_val]
    rfl
  by_cases hpred : i.val + 1 = j.val
  · refine ⟨1, i.castSucc, ?_⟩
    simp only [map_one, one_mul, Fin.val_castSucc]
    rw [← letter_val (n + 1) i, ← hpred]
    exact bubble_mul_pred (letter (n + 1)) (n + 1) i.val i.isLt
  by_cases hself : i.val = j.val
  · refine ⟨1, i.succ, ?_⟩
    simp only [map_one, one_mul, Fin.val_succ]
    rw [← hself, ← letter_val (n + 1) i]
    exact bubble_mul_self (letter (n + 1)) (n + 1) i.val i.isLt
      (letter_square (n + 1) i.val i.isLt)
  · have hhigh : j.val < i.val := by omega
    have hi : i.val - 1 < n := by have := i.isLt; omega
    refine ⟨simple n ⟨i.val - 1, hi⟩, j, ?_⟩
    rw [← letter_val (n + 1) i]
    rw [bubble_mul_high (letter (n + 1)) (n + 1) j.val i.val hhigh i.isLt
      (fun k l hk hl hkl => letter_commute (n + 1) k l hk hl hkl)
      (fun k hk => letter_braid (n + 1) k hk)]
    rw [includePrev_simple, ← letter_val]
    rfl

/-- The canonical finite family of descending coset representatives. -/
def normalForm (n : ℕ) (p : Group n × Fin (n + 2)) : Group (n + 1) :=
  includePrev n p.1 * bubble (letter (n + 1)) (n + 1) p.2.val

/-- Every presented element has a smaller-rank factor and one descending bubble word. -/
theorem normalForm_surjective (n : ℕ) : Function.Surjective (normalForm n) := by
  intro g
  refine Submonoid.induction_of_closure_eq_top_right (simple_mclosure (n + 1)) g ?_ ?_
  · refine ⟨(1, Fin.last (n + 1)), ?_⟩
    simp only [normalForm, map_one, one_mul, Fin.val_last]
    exact bubble_eq_one (letter (n + 1)) (n + 1) (n + 1) le_rfl
  · intro x y hy hx
    rcases hy with ⟨i, rfl⟩
    rcases hx with ⟨⟨v, j⟩, rfl⟩
    obtain ⟨u, k, hk⟩ := bubble_mul_simple n j i
    refine ⟨(v * u, k), ?_⟩
    simp only [normalForm, map_mul]
    rw [mul_assoc, ← hk, ← mul_assoc]

lemma group_zero_eq_one (g : Group 0) : g = 1 := by
  have hm : g ∈ (⊥ : Subgroup (Group 0)) :=
    PresentedGroup.generated_by (relations 0) ⊥ (fun i => Fin.elim0 i) g
  exact hm

/-- The bubble coset cover proves the factorial cardinal bound, including finiteness. -/
theorem finite_card_bound (n : ℕ) :
    Finite (Group n) ∧ Nat.card (Group n) ≤ (n + 1).factorial := by
  induction n with
  | zero =>
      have : Subsingleton (Group 0) :=
        ⟨fun a b => (group_zero_eq_one a).trans (group_zero_eq_one b).symm⟩
      refine ⟨inferInstance, ?_⟩
      rw [Nat.card_of_subsingleton (1 : Group 0)]
      decide
  | succ n ih =>
      have : Finite (Group n) := ih.1
      have : Finite (Group (n + 1)) :=
        Finite.of_surjective (normalForm n) (normalForm_surjective n)
      refine ⟨inferInstance, ?_⟩
      have hb := Nat.card_le_card_of_surjective (normalForm n) (normalForm_surjective n)
      rw [Nat.card_prod, Nat.card_fin] at hb
      calc
        Nat.card (Group (n + 1)) ≤ Nat.card (Group n) * (n + 2) := hb
        _ ≤ (n + 1).factorial * (n + 2) := Nat.mul_le_mul_right (n + 2) ih.2
        _ = (n + 1 + 1).factorial := by rw [Nat.factorial_succ (n + 1), Nat.mul_comm]

theorem toPerm_bijective (n : ℕ) : Function.Bijective (toPerm n) := by
  have : Finite (Group n) := (finite_card_bound n).1
  apply (toPerm_surjective n).bijective_of_nat_card_le
  simpa only [Nat.card_perm, Nat.card_fin] using (finite_card_bound n).2

lemma card_group (n : ℕ) : Nat.card (Group n) = (n + 1).factorial := by
  have hc := Nat.card_eq_of_bijective (toPerm n) (toPerm_bijective n)
  simpa only [Nat.card_perm, Nat.card_fin] using hc

/-- The coset normal form is unique, so its inverse gives canonical finite coordinates. -/
theorem normalForm_bijective (n : ℕ) : Function.Bijective (normalForm n) := by
  have : Finite (Group n) := (finite_card_bound n).1
  apply (normalForm_surjective n).bijective_of_nat_card_le
  rw [Nat.card_prod, Nat.card_fin, card_group n, card_group (n + 1),
    Nat.factorial_succ (n + 1), Nat.mul_comm]

/-- Canonical smaller-rank and bubble-index coordinates of every presented element. -/
def normalFormEquiv (n : ℕ) : Group n × Fin (n + 2) ≃ Group (n + 1) :=
  Equiv.ofBijective (normalForm n) (normalForm_bijective n)

/-- The actual marked isomorphism from the explicit presentation to native permutations. -/
def presentationEquiv (n : ℕ) : Group n ≃* Equiv.Perm (Fin (n + 1)) :=
  MulEquiv.ofBijective (toPerm n) (toPerm_bijective n)

@[simp] lemma presentationEquiv_simple (n : ℕ) (i : Fin n) :
    presentationEquiv n (simple n i) = Equiv.swap i.castSucc i.succ := toPerm_simple n i

@[simp] lemma presentationEquiv_symm_adjacentSwap (n : ℕ) (i : Fin n) :
    (presentationEquiv n).symm (Equiv.swap i.castSucc i.succ) = simple n i := by
  apply (presentationEquiv n).injective
  rw [MulEquiv.apply_symm_apply, presentationEquiv_simple]

section PermLift

variable {n : ℕ} {G : Type*} [_root_.Group G] (s : Fin n → G)
    (hsq : ∀ i, s i * s i = 1)
    (hcomm : ∀ i j, i.val + 1 < j.val → Commute (s i) (s j))
    (hbraid : ∀ i j, i.val + 1 = j.val → s i * s j * s i = s j * s i * s j)

/-- Actual finite permutations lift uniquely through marked type-A generator data. -/
def permLift : Equiv.Perm (Fin (n + 1)) →* G :=
  (lift s hsq hcomm hbraid).comp (presentationEquiv n).symm.toMonoidHom

@[simp] lemma permLift_adjacentSwap (i : Fin n) :
    permLift s hsq hcomm hbraid (Equiv.swap i.castSucc i.succ) = s i := by
  change lift s hsq hcomm hbraid ((presentationEquiv n).symm
    (Equiv.swap i.castSucc i.succ)) = s i
  rw [presentationEquiv_symm_adjacentSwap, lift_simple]

lemma permLift_unique (f : Equiv.Perm (Fin (n + 1)) →* G)
    (hf : ∀ i : Fin n, f (Equiv.swap i.castSucc i.succ) = s i) :
    f = permLift s hsq hcomm hbraid := by
  apply MonoidHom.eq_of_eqOn_denseM (Equiv.Perm.mclosure_swap_castSucc_succ n)
  rintro _ ⟨i, rfl⟩
  rw [hf, permLift_adjacentSwap]

include hsq hcomm hbraid

/-- A group generated by marked type-A generators has an injective native projection. -/
theorem projection_injective_of_generated
    (hgen : Subgroup.closure (Set.range s) = ⊤)
    (f : G →* Equiv.Perm (Fin (n + 1)))
    (hf : ∀ i, f (s i) = Equiv.swap i.castSucc i.succ) : Function.Injective f := by
  have hl : (permLift s hsq hcomm hbraid).comp f = MonoidHom.id G := by
    apply MonoidHom.eq_of_eqOn_dense hgen
    rintro _ ⟨i, rfl⟩
    change permLift s hsq hcomm hbraid (f (s i)) = s i
    rw [hf, permLift_adjacentSwap]
  intro a b hab
  calc
    a = permLift s hsq hcomm hbraid (f a) := (DFunLike.congr_fun hl a).symm
    _ = permLift s hsq hcomm hbraid (f b) := congrArg (permLift s hsq hcomm hbraid) hab
    _ = b := DFunLike.congr_fun hl b

end PermLift

end Equiv.Perm.AdjacentPresentation

end

end
