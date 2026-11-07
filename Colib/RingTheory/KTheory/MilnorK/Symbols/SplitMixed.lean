/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Symbols.Relations
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.Polynomial.Splits
public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.BassTate

/-!
# Split evaluations and the actual mixed-symbol span

All symbols and homogeneous groups below are the native Stacks objects. The
only new mathematical object is an integer submodule of the actual homogeneous
Milnor group. The proof uses no polynomial filtration or specialization map.
In particular no strict/non-strict filtration-index conversion is involved.
Repeated linear factors contribute the native `{-1}` term; they do not vanish.

This is a direct evaluated-symbol proof of the split-generation step in
`Aglib.KTheory.MilnorK.SplitPolynomialGeneration` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`. It does not copy that source's
strict-index filtration or specialization construction.

-/

@[expose] public noncomputable section

universe u v

open Polynomial
open Stacks.Chow

variable {k : Type u} {E : Type v} [Field k] [Field E]

/-- The actual integer span of symbols with a base-field prefix and one final
extension-field unit. -/
@[colib_tag "COL-0226"]
def milnorKMixedSpan (φ : k →+* E) (m : ℕ) :
    Submodule ℤ (MilnorKTheory E (m + 1)) :=
  Submodule.span ℤ (Set.range fun ab : (Fin m → kˣ) × Eˣ =>
    milnorKTupleSymbol (Fin.snoc (Units.map φ.toMonoidHom ∘ ab.1) ab.2))

/-- Membership provides literal finite integer coefficients and actual units. -/
@[colib_tag "COL-0226",
  colib_ref "aglib_principal_euler_pin" "KTheory/MilnorK/SplitPolynomialGeneration.lean:146-162"
    "adaptation"
    "Actual finite integer coefficients in the native homogeneous group"]
theorem milnorKMixedSpan_exists_finsupp (φ : k →+* E) (m : ℕ)
    (x : MilnorKTheory E (m + 1)) (hx : x ∈ milnorKMixedSpan φ m) :
    ∃ c : ((Fin m → kˣ) × Eˣ) →₀ ℤ,
      (c.sum fun ab z => z • milnorKTupleSymbol
        (Fin.snoc (Units.map φ.toMonoidHom ∘ ab.1) ab.2)) = x :=
  Finsupp.mem_span_range_iff_exists_finsupp.mp hx

/-- A base prefix followed by any unit is one of the generators. -/
theorem milnorKTupleSymbol_snoc_mem_mixedSpan (φ : k →+* E) (m : ℕ)
    (a : Fin m → kˣ) (b : Eˣ) :
    milnorKTupleSymbol (Fin.snoc (Units.map φ.toMonoidHom ∘ a) b) ∈
      milnorKMixedSpan φ m :=
  Submodule.subset_span ⟨(a, b), rfl⟩

private theorem splitMixed_move (x : Eˣ) (c l : List Eˣ) :
    (x :: (c ++ l)).Perm (c ++ x :: l) := by
  induction c with
  | nil => exact List.Perm.refl _
  | cons y c ih =>
      exact (List.Perm.swap y x (c ++ l)).trans (ih.cons y)

/-- Partition a word into base units and linear evaluations, preserving its
order up to permutation. This is only a list lemma, not a presentation. -/
private theorem splitMixed_partition (φ : k →+* E) (θ : E) (l : List Eˣ)
    (hl : ∀ z ∈ l, (∃ b : kˣ, Units.map φ.toMonoidHom b = z) ∨
      ∃ a : k, (z : E) = θ - φ a) :
    ∃ (c : List kˣ) (r : List Eˣ),
      l.Perm (c.map (Units.map φ.toMonoidHom) ++ r) ∧
      (∀ z ∈ r, ∃ a : k, (z : E) = θ - φ a) := by
  induction l with
  | nil => exact ⟨[], [], List.Perm.refl [], by simp⟩
  | cons z l ih =>
      obtain ⟨c, r, hp, hr⟩ := ih (fun w hw => hl w (by simp [hw]))
      rcases hl z (by simp) with ⟨b, rfl⟩ | hz
      · exact ⟨b :: c, r, hp.cons _, hr⟩
      · refine ⟨c, z :: r, (hp.cons z).trans (splitMixed_move z _ _), ?_⟩
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact hz
        · exact hr w hw

/-- The Bass--Tate reduction for a word already partitioned into constants and
linear evaluations. Its target is an arbitrary actual additive subgroup. -/
private theorem splitMixed_linear_word (φ : k →+* E) (θ : E) (m : ℕ)
    (H : AddSubgroup (MilnorKRing E))
    (hH : ∀ (c : List kˣ) (b : Eˣ), c.length = m →
      milnorKSymbolProd E (c.map (Units.map φ.toMonoidHom) ++ [b]) ∈ H) :
    ∀ (c : List kˣ) (r : List Eˣ),
      c.length + r.length = m + 1 →
      (∀ z ∈ r, ∃ a : k, (z : E) = θ - φ a) →
      milnorKSymbolProd E (c.map (Units.map φ.toMonoidHom) ++ r) ∈ H := by
  have aux : ∀ n : ℕ, ∀ (c : List kˣ) (r : List Eˣ), r.length = n →
      c.length + r.length = m + 1 →
      (∀ z ∈ r, ∃ a : k, (z : E) = θ - φ a) →
      milnorKSymbolProd E (c.map (Units.map φ.toMonoidHom) ++ r) ∈ H := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c r hn hlen hr
      cases r with
      | nil =>
        cases c with
        | nil => simp at hlen
        | cons b c =>
          apply milnorKSymbolProd_mem_of_perm
            (splitMixed_move (Units.map φ.toMonoidHom b)
              (c.map (Units.map φ.toMonoidHom)) [])
          exact hH c _ (by simpa using hlen)
      | cons x r =>
        cases r with
        | nil => exact hH c x (by simpa using hlen)
        | cons y r =>
          obtain ⟨a, ha⟩ := hr x (by simp)
          obtain ⟨b, hb⟩ := hr y (by simp)
          have hrest : ∀ z ∈ r, ∃ a : k, (z : E) = θ - φ a :=
            fun z hz => hr z (by simp [hz])
          have hterm (z : Eˣ) (hz : ∃ a : k, (z : E) = θ - φ a) (d : kˣ) :
              milnorKSymbolProd E
                (c.map (Units.map φ.toMonoidHom) ++ z :: Units.map φ.toMonoidHom d :: r)
                ∈ H := by
            apply milnorKSymbolProd_mem_of_perm
              ((List.Perm.swap (Units.map φ.toMonoidHom d) z r).append_left
                (c.map (Units.map φ.toMonoidHom)))
            have hh := ih (z :: r).length
              (by simp only [List.length_cons] at hn ⊢; omega)
              (c ++ [d]) (z :: r) rfl
              (by simp only [List.length_append, List.length_cons, List.length_nil]
                    at hlen ⊢
                  omega)
              (by intro w hw; rcases List.mem_cons.mp hw with rfl | hw
                  · exact hz
                  · exact hrest w hw)
            simpa [List.map_append, List.append_assoc] using hh
          have hneg : Units.map φ.toMonoidHom (-1 : kˣ) = (-1 : Eˣ) := by
            apply Units.ext
            simp
          have hyneg := hterm y ⟨b, hb⟩ (-1)
          rw [hneg] at hyneg
          by_cases hab : a = b
          · have hxy : x = y := Units.ext (by rw [ha, hb, hab])
            subst x
            have heq :
                milnorKSymbolProd E (c.map (Units.map φ.toMonoidHom) ++ y :: y :: r) =
                  -milnorKSymbolProd E
                    (c.map (Units.map φ.toMonoidHom) ++ y :: (-1 : Eˣ) :: r) := by
              simp only [milnorKSymbolProd_append, milnorKSymbolProd_cons]
              rw [← mul_assoc (milnorKSymbol E y),
                eq_neg_of_add_eq_zero_left (milnorKSymbol_mul_self_add_mul_negOne (k := E) y),
                milnorKNegOne_eq]
              simp only [neg_mul, mul_neg, mul_assoc]
            rw [heq]
            exact H.neg_mem hyneg
          · let d : kˣ := Units.mk0 (a - b) (sub_ne_zero.mpr hab)
            have hadd : (x : E) + (Units.map φ.toMonoidHom d : E) = (y : E) := by
              change (x : E) + φ (a - b) = (y : E)
              rw [ha, hb, map_sub]
              ring
            have hx := hterm x ⟨a, ha⟩ d
            have hy := hterm y ⟨b, hb⟩ d
            have heq :
                milnorKSymbolProd E (c.map (Units.map φ.toMonoidHom) ++ x :: y :: r) =
                  milnorKSymbolProd E
                    (c.map (Units.map φ.toMonoidHom) ++ x :: Units.map φ.toMonoidHom d :: r) -
                  milnorKSymbolProd E
                    (c.map (Units.map φ.toMonoidHom) ++ y :: Units.map φ.toMonoidHom d :: r) -
                  milnorKSymbolProd E
                    (c.map (Units.map φ.toMonoidHom) ++ y :: (-1 : Eˣ) :: r) := by
              simp only [milnorKSymbolProd_append, milnorKSymbolProd_cons]
              rw [← mul_assoc (milnorKSymbol E x), milnorKSymbol_mul_of_add_eq' hadd]
              simp only [sub_mul, mul_sub, milnorKNegOne_eq, mul_assoc]
            rw [heq]
            exact H.sub_mem (H.sub_mem hx hy) hyneg
  intro c r hlen hr
  exact aux r.length c r rfl hlen hr

/-- Coordinatewise additive closure can be expanded inside an arbitrary
subgroup while preserving the exact number of entries. -/
private theorem splitMixed_word_closure (S : Set Eˣ)
    (l : List Eˣ) (H : AddSubgroup (MilnorKRing E))
    (hl : ∀ z ∈ l, milnorKSymbol E z ∈ AddSubgroup.closure (milnorKSymbol E '' S))
    (hH : ∀ r : List Eˣ, r.length = l.length → (∀ z ∈ r, z ∈ S) →
      milnorKSymbolProd E r ∈ H) : milnorKSymbolProd E l ∈ H := by
  induction l generalizing H with
  | nil => exact hH [] rfl (by simp)
  | cons z l ih =>
    have htail := fun w hw => hl w (List.mem_cons_of_mem z hw)
    have key : milnorKSymbol E z ∈
        H.comap (AddMonoidHom.mulRight (milnorKSymbolProd E l)) := by
      refine (AddSubgroup.closure_le _).mpr ?_ (hl z List.mem_cons_self)
      rintro _ ⟨b, hb, rfl⟩
      exact ih (H.comap (AddMonoidHom.mulLeft (milnorKSymbol E b))) htail
        (fun r hlen hr => hH (b :: r) (by simp [hlen]) (by
          intro w hw
          rcases List.mem_cons.mp hw with rfl | hw
          · exact hb
          · exact hr w hw))
    exact key

private theorem splitMixed_symbol_aeval [Algebra k E] (θ : E)
    (q : k[X]) (hs : q.Splits) (hne : aeval θ q ≠ 0) :
    milnorKSymbol E (Units.mk0 (aeval θ q) hne) ∈
      AddSubgroup.closure (milnorKSymbol E ''
        {z : Eˣ | (∃ b : kˣ, Units.map (algebraMap k E).toMonoidHom b = z) ∨
          ∃ a : k, (z : E) = θ - algebraMap k E a}) := by
  revert hne
  induction hs using Submonoid.closure_induction with
  | mem q hq =>
    intro hne
    apply AddSubgroup.subset_closure
    refine ⟨_, ?_, rfl⟩
    rcases hq with ⟨c, rfl⟩ | ⟨a, rfl⟩
    · left
      have hc : c ≠ 0 := by
        intro h
        apply hne
        simp [h]
      refine ⟨Units.mk0 c hc, ?_⟩
      apply Units.ext
      simp
    · right
      exact ⟨-a, by simp⟩
  | one =>
    intro hne
    have hu : Units.mk0 (aeval θ (1 : k[X])) hne = 1 := by
      apply Units.ext
      simp
    rw [hu, milnorKSymbol_one]
    exact AddSubgroup.zero_mem _
  | mul q r _ _ ihq ihr =>
    intro hne
    have hq : aeval θ q ≠ 0 := left_ne_zero_of_mul (by simpa using hne)
    have hr : aeval θ r ≠ 0 := right_ne_zero_of_mul (by simpa using hne)
    have hu : Units.mk0 (aeval θ (q * r)) hne =
        Units.mk0 (aeval θ q) hq * Units.mk0 (aeval θ r) hr := by
      apply Units.ext
      simp
    rw [hu, milnorKSymbol_mul]
    exact add_mem (ihq hq) (ihr hr)

/-- Evaluating finitely many split polynomials produces an actual mixed
symbol class. The field universes are independent; no irreducible modulus,
separability, norm or global generation assumption is needed. -/
@[colib_tag "COL-0226",
  colib_ref "aglib_principal_euler_pin" "KTheory/MilnorK/SplitPolynomialGeneration.lean:74-80"
    "adaptation"
    "Direct native evaluated-symbol proof, with no filtration or specialization",
  colib_ref "axiom_stacks"
    "StacksFrontier/AlgebraicGeometry/Chow/MilnorNorm/BassTate.lean:99-105"
    "ingredient" "Native two-unit reduction with the negative-one correction"]
theorem milnorKTupleSymbol_aeval_mem_mixedSpan [Algebra k E] (θ : E) (m : ℕ)
    (a : Fin (m + 1) → k[X]) (hsplit : ∀ i, (a i).Splits)
    (hne : ∀ i, aeval θ (a i) ≠ 0) :
    milnorKTupleSymbol (fun i => Units.mk0 (aeval θ (a i)) (hne i)) ∈
      milnorKMixedSpan (algebraMap k E) m := by
  let φ := algebraMap k E
  let M := milnorKMixedSpan φ m
  let H : AddSubgroup (MilnorKRing E) :=
    M.toAddSubgroup.map (milnorKGrading E (m + 1)).subtype
  let S : Set Eˣ := {z | (∃ b : kˣ, Units.map φ.toMonoidHom b = z) ∨
    ∃ t : k, (z : E) = θ - φ t}
  have hH (c : List kˣ) (b : Eˣ) (hc : c.length = m) :
      milnorKSymbolProd E (c.map (Units.map φ.toMonoidHom) ++ [b]) ∈ H := by
    let t : Fin m → kˣ := fun i => c.get (Fin.cast hc.symm i)
    have ht : List.ofFn t = c := by
      subst m
      exact List.ofFn_get c
    refine ⟨milnorKTupleSymbol (Fin.snoc (Units.map φ.toMonoidHom ∘ t) b),
      milnorKTupleSymbol_snoc_mem_mixedSpan φ m t b, ?_⟩
    change milnorKSymbolProd E
      (List.ofFn (Fin.snoc (Units.map φ.toMonoidHom ∘ t) b)) = _
    congr 1
    rw [List.ofFn_succ']
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [← List.map_ofFn, ht]
    simp
  have hgen (r : List Eˣ) (hlen : r.length = m + 1) (hr : ∀ z ∈ r, z ∈ S) :
      milnorKSymbolProd E r ∈ H := by
    obtain ⟨c, l, hp, hl⟩ := splitMixed_partition φ θ r hr
    apply milnorKSymbolProd_mem_of_perm hp
    exact splitMixed_linear_word φ θ m H hH c l
      (by have := hp.length_eq; simp only [List.length_append, List.length_map] at this
          omega) hl
  have hmem : milnorKSymbolProd E
      (List.ofFn fun i => Units.mk0 (aeval θ (a i)) (hne i)) ∈ H := by
    apply splitMixed_word_closure S _ H
    · intro z hz
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      exact splitMixed_symbol_aeval θ (a i) (hsplit i) (hne i)
    · intro r hr hS
      exact hgen r (by simpa using hr) hS
  obtain ⟨y, hy, heq⟩ := hmem
  have hyx : y = milnorKTupleSymbol
      (fun i => Units.mk0 (aeval θ (a i)) (hne i)) := Subtype.ext heq
  exact hyx ▸ hy
