/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Mathlib.Algebra.Field.Defs
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.PresentedGroup

/-!
# The finite-rank presentation of the stable Steinberg group

The generators are finite-rank roots `(n, i, j, a)` with `i ≠ j`. Mathlib's
`PresentedGroup` imposes root addition, disjoint commutation, the ordered chain
relation and standard one-coordinate stabilization. These same generators and
relators occur in the pinned Quillen source. They define the single Steinberg
presentation selected here, without a second quotient or an adapter model.

A fresh final index expresses every generator as a commutator. Thus this actual
presentation is perfect over every field, including fields with two or three
elements. No identification of its kernel with Milnor or Quillen K₂ is asserted.

## Implementation provenance

Adapted from `Quillen/Algebra/Group/StableSteinberg.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, through `isPerfect`. The matrix map,
centrality, universal extension and Matsumoto comparison remain separate work.
-/
@[expose] public section

noncomputable section

universe u

namespace StableSteinberg

open scoped commutatorElement

variable (F : Type u) [Field F]

/-- An off-diagonal root and its coefficient at an actual finite rank. -/
structure Generator where
  /-- The finite rank at which the root is represented. -/
  rank : ℕ
  /-- The row index in that finite rank. -/
  row : Fin rank
  /-- The column index in that finite rank. -/
  col : Fin rank
  /-- The root is off the diagonal. -/
  ne : row ≠ col
  /-- The field coefficient of the root. -/
  entry : F

/-- The corresponding formal generator in the free group of all finite root data. -/
def word (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : F) : FreeGroup (Generator F) :=
  FreeGroup.of ⟨n, i, j, hij, a⟩

/-- The finite Steinberg relators and explicit one-coordinate stabilization relators. -/
inductive Relator : FreeGroup (Generator F) → Prop
  /-- The additive root relation, written as a word equal to one. -/
  | rootAdd (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a b : F) :
      Relator (word F n i j hij a * word F n i j hij b *
        (word F n i j hij (a + b))⁻¹)
  /-- The commutator vanishes when the two roots have no interacting indices. -/
  | disjoint (n : ℕ) (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
      (hjk : j ≠ k) (hli : l ≠ i) (a b : F) :
      Relator ⁅word F n i j hij a, word F n k l hkl b⁆
  /-- The ordered chain commutator has coefficient `a * b`. -/
  | chain (n : ℕ) (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
      (a b : F) :
      Relator (⁅word F n i j hij a, word F n j k hjk b⁆ *
        (word F n i k hik (a * b))⁻¹)
  /-- A finite root is identified with its standard next-rank stabilization. -/
  | stabilize (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : F) :
      Relator (word F n i j hij a *
        (word F (n + 1) i.castSucc j.castSucc (by simpa using hij) a)⁻¹)

/-- The actual set of words imposed as relators in the free group. -/
def relations : Set (FreeGroup (Generator F)) := {r | Relator F r}

/-- The stable Steinberg group in the finite-rank-labelled presentation. -/
abbrev Group := PresentedGroup (relations F)

/-- The root generator at an actual finite rank in the stable Steinberg group. -/
def x (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : F) : Group F :=
  PresentedGroup.of ⟨n, i, j, hij, a⟩

/-- Addition in one root is multiplication of its presented generators. -/
lemma x_add (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a b : F) :
    x F n i j hij a * x F n i j hij b = x F n i j hij (a + b) := by
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relations F)
    (Relator.rootAdd (F := F) n i j hij a b)
  simpa only [word, x, PresentedGroup.of, map_mul] using h

/-- Root generators with disjoint interacting indices commute. -/
lemma x_commute (n : ℕ) (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i) (a b : F) :
    Commute (x F n i j hij a) (x F n k l hkl b) := by
  apply commutatorElement_eq_one_iff_commute.mp
  have h := PresentedGroup.one_of_mem (rels := relations F)
    (Relator.disjoint (F := F) n i j k l hij hkl hjk hli a b)
  simpa only [word, x, PresentedGroup.of, map_commutatorElement] using h

/-- The ordered Steinberg chain relation in the presented group. -/
lemma x_commutator (n : ℕ) (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a b : F) :
    ⁅x F n i j hij a, x F n j k hjk b⁆ = x F n i k hik (a * b) := by
  have h := PresentedGroup.mk_eq_mk_of_mul_inv_mem (rels := relations F)
    (Relator.chain (F := F) n i j k hij hjk hik a b)
  simpa only [word, x, PresentedGroup.of, map_commutatorElement] using h

/-- A root generator agrees with its actual next-rank stabilization. -/
lemma x_stabilize (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : F) :
    x F n i j hij a = x F (n + 1) i.castSucc j.castSucc (by simpa using hij) a := by
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (Relator.stabilize (F := F) n i j hij a)

/-- The root generator with coefficient zero is the identity. -/
lemma x_zero (n : ℕ) (i j : Fin n) (hij : i ≠ j) : x F n i j hij 0 = 1 := by
  apply mul_left_cancel (a := x F n i j hij 0)
  simpa only [zero_add, mul_one] using x_add F n i j hij 0 0

/-- Every root generator is a commutator after adjoining one actual coordinate. -/
lemma x_eq_commutator_succ (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : F) :
    x F n i j hij a =
      ⁅x F (n + 1) i.castSucc (Fin.last n) (Fin.castSucc_ne_last i) a,
        x F (n + 1) (Fin.last n) j.castSucc (Fin.castSucc_ne_last j).symm 1⁆ := by
  rw [x_commutator F (n + 1) i.castSucc (Fin.last n) j.castSucc
    (Fin.castSucc_ne_last i) (Fin.castSucc_ne_last j).symm (by simpa using hij), mul_one]
  exact x_stabilize F n i j hij a

/-- The stable Steinberg presentation is perfect over every field. -/
instance isPerfect : _root_.Group.IsPerfect (Group F) where
  commutator_eq_top := by
    apply top_unique
    intro g _
    apply PresentedGroup.generated_by (relations F) (commutator (Group F)) _ g
    rintro ⟨n, i, j, hij, a⟩
    change x F n i j hij a ∈ commutator (Group F)
    rw [x_eq_commutator_succ]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

end StableSteinberg
