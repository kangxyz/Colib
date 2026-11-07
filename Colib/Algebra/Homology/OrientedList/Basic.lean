/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.Data.List.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Abel

/-!
Adapted from `Quillen/Topology/LocalCoefficients/SubdivisionListChains.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps and signs.

# The explicit augmented oriented-list chain algebra

Generators are finite ordered lists of actual points. The empty list is the
augmentation generator, and the boundary is the alternating deletion boundary.
Prepending a point gives the actual cone operator. Subdivision is constructed
recursively by coning the already subdivided boundary to a specified center.
No chain-map or homotopy identity is part of the input data.
-/

@[expose] public section

noncomputable section

namespace FreeAbelianGroup.OrientedList

universe u v

variable {P : Type u}

/-- Augmented finite oriented chains of points. -/
abbrev Chain (P : Type u) := FreeAbelianGroup (List P)

/-- A single ordered simplex, including the empty augmentation simplex. -/
abbrev generator (l : List P) : Chain P := FreeAbelianGroup.of l

/-- The cone consists of prepending its specified vertex. -/
def cone (p : P) : Chain P →+ Chain P := FreeAbelianGroup.map (List.cons p)

@[simp]
theorem cone_generator (p : P) (l : List P) :
    cone p (generator l) = generator (p :: l) := FreeAbelianGroup.map_of_apply _

/-- Boundary on a generator, with the usual alternating orientation. -/
def boundaryGenerator : List P → Chain P
  | [] => 0
  | p :: l => generator l - cone p (boundaryGenerator l)

/-- The additive extension of the explicit deletion boundary. -/
def boundary : Chain P →+ Chain P := FreeAbelianGroup.lift boundaryGenerator

theorem boundary_generator (l : List P) :
    boundary (generator l) = boundaryGenerator l := FreeAbelianGroup.lift_apply_of _ _

@[simp]
theorem boundary_nil : boundary (generator ([] : List P)) = 0 := by
  rw [boundary_generator]; rfl

@[simp]
theorem boundary_cons (p : P) (l : List P) :
    boundary (generator (p :: l)) = generator l - cone p (boundary (generator l)) := by
  rw [boundary_generator, boundary_generator]; rfl

/-- The cone identity is an identity of actual finite chains. -/
theorem boundary_cone (p : P) (c : Chain P) :
    boundary (cone p c) = c - cone p (boundary c) := by
  induction c using FreeAbelianGroup.induction_on with
  | zero => simp
  | of l => simp
  | neg c hc => simp only [map_neg, hc]; abel
  | add c d hc hd => simp only [map_add, hc, hd]; abel

/-- Consecutive alternating deletion boundaries cancel. -/
@[simp]
theorem boundary_boundary (c : Chain P) : boundary (boundary c) = 0 := by
  suffices h : ∀ l : List P, boundary (boundary (generator l)) = 0 by
    induction c using FreeAbelianGroup.induction_on with
    | zero => simp
    | of l => exact h l
    | neg c hc => simp [hc]
    | add c d hc hd => simp [hc, hd]
  intro l
  induction l with
  | nil => simp
  | cons p l ih => rw [boundary_cons, map_sub, boundary_cone, ih]; simp

/-- The recursive deletion boundary is exactly the signed sum of all faces. -/
theorem boundary_generator_eq_sum (l : List P) :
    boundary (generator l) =
      ∑ i : Fin l.length, (-1 : ℤ) ^ i.val • generator (l.eraseIdx i.val) := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [boundary_cons, ih, map_sum]
    change _ = ∑ i : Fin (l.length + 1), _
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, List.eraseIdx_zero, one_zsmul,
      Fin.val_succ, List.eraseIdx_cons_succ, pow_succ, mul_neg_one]
    simp only [map_zsmul, cone_generator, neg_zsmul]
    rw [Finset.sum_neg_distrib]
    simp only [List.tail_cons, sub_eq_add_neg]

/-- A boundary depends only on values on lists with one fewer vertex. -/
theorem hom_eq_on_boundary {G : Type v} [AddCommGroup G]
    (f g : Chain P →+ G) (l : List P)
    (h : ∀ k : List P, k.length + 1 = l.length → f (generator k) = g (generator k)) :
    f (boundary (generator l)) = g (boundary (generator l)) := by
  rw [boundary_generator_eq_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul, map_zsmul, h _ (List.length_eraseIdx_add_one i.isLt)]

/-- Recursive coning of the subdivided alternating boundary. The center is an
actual chosen point, and no identity is required of this choice. -/
def subdivisionGenerator (center : List P → P) (l : List P) : Chain P :=
  if l = [] then generator [] else
    cone (center l)
      (∑ i : Fin l.length,
        (-1 : ℤ) ^ i.val • subdivisionGenerator center (l.eraseIdx i.val))
termination_by l.length
decreasing_by
  have := List.length_eraseIdx_add_one i.isLt
  omega

/-- Actual subdivision on finite oriented chains. -/
def subdivision (center : List P → P) : Chain P →+ Chain P :=
  FreeAbelianGroup.lift (subdivisionGenerator center)

@[simp]
theorem subdivision_generator (center : List P → P) (l : List P) :
    subdivision center (generator l) = subdivisionGenerator center l :=
  FreeAbelianGroup.lift_apply_of _ _

@[simp]
theorem subdivisionGenerator_nil (center : List P → P) :
    subdivisionGenerator center [] = generator [] := by
  rw [subdivisionGenerator, ite_eq_left rfl]

/-- The defining subdivision equation, expressed using the actual boundary. -/
theorem subdivision_generator_nonempty (center : List P → P) (l : List P)
    (hl : l ≠ []) :
    subdivision center (generator l) =
      cone (center l) (subdivision center (boundary (generator l))) := by
  rw [subdivision_generator, subdivisionGenerator, ite_eq_right hl,
    boundary_generator_eq_sum]
  simp only [map_sum, map_zsmul, subdivision_generator]

/-- Recursive coning produces a chain map, with no assumed cancellation identities. -/
theorem boundary_subdivision (center : List P → P) (c : Chain P) :
    boundary (subdivision center c) = subdivision center (boundary c) := by
  suffices h : ∀ l : List P,
      boundary (subdivision center (generator l)) =
        subdivision center (boundary (generator l)) by
    induction c using FreeAbelianGroup.induction_on with
    | zero => simp
    | of l => exact h l
    | neg l hl => simpa only [map_neg] using congrArg Neg.neg hl
    | add c d hc hd => simp only [map_add, hc, hd]
  intro l
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | h n ih =>
    by_cases hl : l = []
    · subst l; simp
    · rw [subdivision_generator_nonempty center l hl, boundary_cone]
      have heq := hom_eq_on_boundary
        (boundary.comp (subdivision center)) ((subdivision center).comp boundary) l
        (fun k hk ↦ ih k.length (by omega) k rfl)
      change boundary (subdivision center (boundary (generator l))) =
        subdivision center (boundary (boundary (generator l))) at heq
      rw [heq, boundary_boundary, map_zero, map_zero, sub_zero]

/-- The actual recursively coned homotopy from subdivision to identity. -/
def homotopyGenerator (center : List P → P) (l : List P) : Chain P :=
  if l = [] then 0 else
    cone (center l)
      (generator l - subdivision center (generator l) -
        ∑ i : Fin l.length,
          (-1 : ℤ) ^ i.val • homotopyGenerator center (l.eraseIdx i.val))
termination_by l.length
decreasing_by
  have := List.length_eraseIdx_add_one i.isLt
  omega

/-- Additive extension of the concrete recursively coned homotopy. -/
def homotopy (center : List P → P) : Chain P →+ Chain P :=
  FreeAbelianGroup.lift (homotopyGenerator center)

@[simp]
theorem homotopy_generator (center : List P → P) (l : List P) :
    homotopy center (generator l) = homotopyGenerator center l :=
  FreeAbelianGroup.lift_apply_of _ _

@[simp]
theorem homotopyGenerator_nil (center : List P → P) :
    homotopyGenerator center [] = 0 := by
  rw [homotopyGenerator, ite_eq_left rfl]

/-- The recursive homotopy formula uses the subdivided simplex and all its faces. -/
theorem homotopy_generator_nonempty (center : List P → P) (l : List P)
    (hl : l ≠ []) :
    homotopy center (generator l) =
      cone (center l) (generator l - subdivision center (generator l) -
        homotopy center (boundary (generator l))) := by
  rw [homotopy_generator, homotopyGenerator, ite_eq_right hl,
    boundary_generator_eq_sum]
  simp only [map_sub, map_sum, map_zsmul, homotopy_generator]

/-- The constructed subdivision is chain homotopic to the actual identity. -/
theorem boundary_homotopy_add_homotopy_boundary (center : List P → P) (c : Chain P) :
    boundary (homotopy center c) + homotopy center (boundary c) =
      c - subdivision center c := by
  suffices h : ∀ l : List P,
      boundary (homotopy center (generator l)) +
          homotopy center (boundary (generator l)) =
        generator l - subdivision center (generator l) by
    induction c using FreeAbelianGroup.induction_on with
    | zero => simp
    | of l => exact h l
    | neg l hl =>
      simp only [map_neg]
      rw [← neg_add, hl]
      abel
    | add c d hc hd =>
      simp only [map_add]
      rw [add_add_add_comm, hc, hd]
      abel
  intro l
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | h n ih =>
    by_cases hl : l = []
    · subst l; simp
    · rw [homotopy_generator_nonempty center l hl, boundary_cone]
      have heq := hom_eq_on_boundary
        (boundary.comp (homotopy center) + (homotopy center).comp boundary)
        (AddMonoidHom.id _ - subdivision center) l
        (fun k hk ↦ ih k.length (by omega) k rfl)
      change boundary (homotopy center (boundary (generator l))) +
          homotopy center (boundary (boundary (generator l))) =
        boundary (generator l) - subdivision center (boundary (generator l)) at heq
      rw [boundary_boundary, map_zero, add_zero] at heq
      simp only [map_sub, boundary_subdivision, heq, sub_self, map_zero, sub_zero]
      abel

/-- Apply a point map to every vertex, retaining the ordering and coefficients. -/
def mapPoints {Q : Type v} (f : P → Q) : Chain P →+ Chain Q :=
  FreeAbelianGroup.map (List.map f)

@[simp]
theorem mapPoints_generator {Q : Type v} (f : P → Q) (l : List P) :
    mapPoints f (generator l) = generator (l.map f) :=
  FreeAbelianGroup.map_of_apply _

@[simp]
theorem mapPoints_cone {Q : Type v} (f : P → Q) (p : P) (c : Chain P) :
    mapPoints f (cone p c) = cone (f p) (mapPoints f c) := by
  induction c using FreeAbelianGroup.induction_on with
  | zero => simp
  | of l => simp
  | neg l hl => simpa only [map_neg] using congrArg Neg.neg hl
  | add c d hc hd => simp only [map_add, hc, hd]

/-- Point maps commute with the actual alternating boundary. -/
theorem mapPoints_boundary {Q : Type v} (f : P → Q) (c : Chain P) :
    mapPoints f (boundary c) = boundary (mapPoints f c) := by
  suffices h : ∀ l : List P,
      mapPoints f (boundary (generator l)) = boundary (mapPoints f (generator l)) by
    induction c using FreeAbelianGroup.induction_on with
    | zero => simp
    | of l => exact h l
    | neg l hl => simpa only [map_neg] using congrArg Neg.neg hl
    | add c d hc hd => simp only [map_add, hc, hd]
  intro l
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [boundary_cons, map_sub, mapPoints_cone, mapPoints_generator, List.map_cons]
    rw [ih, mapPoints_generator]

/-- Subdivision is natural for point maps preserving the chosen nonempty centers. -/
theorem mapPoints_subdivision {Q : Type v} (f : P → Q)
    (centerP : List P → P) (centerQ : List Q → Q)
    (hf : ∀ l : List P, l ≠ [] → centerQ (l.map f) = f (centerP l))
    (c : Chain P) :
    mapPoints f (subdivision centerP c) = subdivision centerQ (mapPoints f c) := by
  suffices h : ∀ l : List P,
      mapPoints f (subdivision centerP (generator l)) =
        subdivision centerQ (mapPoints f (generator l)) by
    induction c using FreeAbelianGroup.induction_on with
    | zero => simp
    | of l => exact h l
    | neg l hl => simpa only [map_neg] using congrArg Neg.neg hl
    | add c d hc hd => simp only [map_add, hc, hd]
  intro l
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | h n ih =>
    by_cases hl : l = []
    · subst l; simp
    · have hmap : l.map f ≠ [] := by simpa using hl
      have heq := hom_eq_on_boundary
        ((mapPoints f).comp (subdivision centerP))
        ((subdivision centerQ).comp (mapPoints f)) l
        (fun k hk ↦ ih k.length (by omega) k rfl)
      change mapPoints f (subdivision centerP (boundary (generator l))) =
        subdivision centerQ (mapPoints f (boundary (generator l))) at heq
      rw [subdivision_generator_nonempty centerP l hl, mapPoints_cone, heq,
        mapPoints_boundary, mapPoints_generator,
        subdivision_generator_nonempty centerQ (l.map f) hmap, hf l hl]

/-- The explicit homotopy has the same naturality as subdivision. -/
theorem mapPoints_homotopy {Q : Type v} (f : P → Q)
    (centerP : List P → P) (centerQ : List Q → Q)
    (hf : ∀ l : List P, l ≠ [] → centerQ (l.map f) = f (centerP l))
    (c : Chain P) :
    mapPoints f (homotopy centerP c) = homotopy centerQ (mapPoints f c) := by
  suffices h : ∀ l : List P,
      mapPoints f (homotopy centerP (generator l)) =
        homotopy centerQ (mapPoints f (generator l)) by
    induction c using FreeAbelianGroup.induction_on with
    | zero => simp
    | of l => exact h l
    | neg l hl => simpa only [map_neg] using congrArg Neg.neg hl
    | add c d hc hd => simp only [map_add, hc, hd]
  intro l
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | h n ih =>
    by_cases hl : l = []
    · subst l; simp
    · have hmap : l.map f ≠ [] := by simpa using hl
      have heq := hom_eq_on_boundary
        ((mapPoints f).comp (homotopy centerP))
        ((homotopy centerQ).comp (mapPoints f)) l
        (fun k hk ↦ ih k.length (by omega) k rfl)
      change mapPoints f (homotopy centerP (boundary (generator l))) =
        homotopy centerQ (mapPoints f (boundary (generator l))) at heq
      rw [homotopy_generator_nonempty centerP l hl, mapPoints_cone,
        mapPoints_generator, homotopy_generator_nonempty centerQ (l.map f) hmap, hf l hl]
      congr 1
      simp only [map_sub, mapPoints_subdivision f centerP centerQ hf, heq,
        mapPoints_boundary, mapPoints_generator]

end FreeAbelianGroup.OrientedList
