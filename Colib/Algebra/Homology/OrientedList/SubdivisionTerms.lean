/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.OrientedList.Support

/-!
Adapted from `Quillen/Topology/LocalCoefficients/SubdivisionTerms.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps and signs.

# Exact recursive support of coning subdivision

Every summand in the constructed subdivision is a descending chain of centers
of successively deleted faces. The inductive predicate records these actual
lists, so geometric estimates can be proved on the support without choosing
an orientation convention for permutation flags.
-/

@[expose] public section

noncomputable section

namespace FreeAbelianGroup.OrientedList

universe u

variable {P : Type u}

/-- One actual descending-face-center term of the recursive subdivision. -/
inductive SubdivisionTerm (center : List P → P) : List P → List P → Prop
  | nil : SubdivisionTerm center [] []
  | cons (l : List P) (hl : l ≠ []) (i : Fin l.length) (k : List P)
      (hk : SubdivisionTerm center (l.eraseIdx i.val) k) :
      SubdivisionTerm center l (center l :: k)

/-- Every term of subdivision has the same number of vertices as its input. -/
theorem SubdivisionTerm.length {center : List P → P} {l k : List P}
    (h : SubdivisionTerm center l k) : k.length = l.length := by
  induction h with
  | nil => rfl
  | cons l hl i k hk ih =>
    simp only [List.length_cons, ih]
    exact List.length_eraseIdx_add_one i.isLt

/-- Exact support of the concrete recursive subdivision operator. -/
theorem subdivision_supported_terms (center : List P → P) (l : List P) :
    Supported (SubdivisionTerm center l) (subdivision center (generator l)) := by
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | h n ih =>
    by_cases hl : l = []
    · subst l
      simp only [subdivision_generator, subdivisionGenerator_nil]
      exact Supported.generator [] SubdivisionTerm.nil
    · rw [subdivision_generator_nonempty center l hl, boundary_generator_eq_sum]
      simp only [map_sum, map_zsmul]
      apply Supported.sum
      intro i _
      apply Supported.zsmul
      have hk := ih (l.eraseIdx i.val).length
        (by have := List.length_eraseIdx_add_one i.isLt; omega) (l.eraseIdx i.val) rfl
      apply hk.map (cone (center l))
      intro k hterm
      rw [cone_generator]
      exact Supported.generator _ (SubdivisionTerm.cons l hl i k hterm)

end FreeAbelianGroup.OrientedList
