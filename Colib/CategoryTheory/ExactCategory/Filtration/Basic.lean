/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.CategoryTheory.ExactCategory.AdditiveInvariant
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Finite admissible filtrations

Finite conflation towers retain their actual short-complex maps, chosen factors,
and zero-object base. The factor list, length and factor-membership laws require
only an exact structure; no Grothendieck or K-theory construction is used.

## Implementation provenance

Adapted from `Quillen/Aglib/CategoryTheory/ExactCategory/Filtration/Basic.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual conflations, arbitrary
zero-object base, independent object and morphism universes, and finite towers
are preserved. This is a prerequisite, not the homotopical dévissage theorem.
-/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section

universe v u w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ExactCategory.ExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- A finite admissible filtration with chosen successive factors satisfying `P`.
The base may be any zero object, so there is no dependence on a particular choice
of zero object. In a step the previous filtered object is the first object of a
conflation and the new final object is its middle object. -/
inductive Filtration (P : C → Prop) : C → Type (max u v)
  | zero {X : C} (hX : IsZero X) : Filtration P X
  | step (S : ShortComplex C) (hS : E.conflation S)
      (previous : Filtration P S.X₁) (factor_mem : P S.X₃) : Filtration P S.X₂

variable {E} {P : C → Prop}

namespace Filtration

/-- The successive factors, listed from the zero object towards the final object. -/
def factors {X : C} : E.Filtration P X → List C
  | .zero _ => []
  | .step S _ previous _ => previous.factors ++ [S.X₃]

/-- The number of conflations in this finite extension tower. -/
def length {X : C} (F : E.Filtration P X) : ℕ := F.factors.length

@[simp] lemma factors_zero {X : C} (hX : IsZero X) :
    (Filtration.zero (E := E) (P := P) hX).factors = [] := rfl

@[simp] lemma factors_step (S : ShortComplex C) (hS : E.conflation S)
    (previous : E.Filtration P S.X₁) (hP : P S.X₃) :
    (Filtration.step S hS previous hP).factors = previous.factors ++ [S.X₃] := rfl

@[simp] lemma length_zero {X : C} (hX : IsZero X) :
    (Filtration.zero (E := E) (P := P) hX).length = 0 := rfl

@[simp] lemma length_step (S : ShortComplex C) (hS : E.conflation S)
    (previous : E.Filtration P S.X₁) (hP : P S.X₃) :
    (Filtration.step S hS previous hP).length = previous.length + 1 := by
  simp [length]

/-- Every recorded factor satisfies the filtration predicate. -/
lemma mem_factors {X : C} (F : E.Filtration P X) {Y : C}
    (hY : Y ∈ F.factors) : P Y := by
  induction F with
  | zero hX => simp at hY
  | step S hS previous hP ih =>
    simp only [factors_step, List.mem_append, List.mem_singleton] at hY
    rcases hY with hY | rfl
    · exact ih hY
    · exact hP

/-- The analogous telescoping formula for every conflation-additive invariant. -/
theorem additiveInvariant_eq_sum {A : Type w} [AddCommGroup A] (f : C → A)
    (hf : E.IsAdditiveInvariant f) {X : C} (F : E.Filtration P X) :
    f X = (F.factors.map f).sum := by
  induction F with
  | zero hX =>
    simpa using (IsAdditiveInvariant.iso E hf (hX.iso (isZero_zero C))).trans
      (IsAdditiveInvariant.zero E hf)
  | step S hS previous hP ih =>
    rw [hf S hS, ih]
    simp

end Filtration

end CategoryTheory.ExactCategory.ExactStructure

attribute [colib_tag "COL-0244",
  colib_ref "WeibelKBook" "V, Devissage Theorem 4.1, finite-filtration hypothesis, page 33"
    "adaptation" "Actual finite conflation towers and telescoping for additive invariants"]
  CategoryTheory.ExactCategory.ExactStructure.Filtration
  CategoryTheory.ExactCategory.ExactStructure.Filtration.factors
  CategoryTheory.ExactCategory.ExactStructure.Filtration.additiveInvariant_eq_sum
