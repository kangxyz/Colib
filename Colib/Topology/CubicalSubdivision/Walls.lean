/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.CubicalSubdivision.Pasting

/-! # The actual grid walls and compatible top-dimensional extension

Grid walls are the images of whole cell boundaries. A continuous lift already
specified on those walls determines compatible boundary data on every cell;
any actual cell fillers paste to a continuous extension of that same wall map.
The lower-dimensional construction of the wall lift is a separate obligation.


Implementation provenance:
`Quillen/Topology/CubicalSubdivision/Walls.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open scoped Topology unitInterval
namespace Topology.CubicalSubdivision
universe u v

/-- The boundary subspace of the unit `n`-cube. -/
abbrev Boundary (n : ℕ) := {t : Cube n // t ∈ _root_.Cube.boundary (Fin n)}

/-- The union of the images of all cell boundaries in the subdivided unit cube. -/
def walls (n m : ℕ) : Set (Cube n) :=
  {x | ∃ k : CellIndex n m, ∃ t : Boundary n, cell n m k t = x}

/-- Map the boundary of a chosen cell into the grid walls by its cell characteristic map. -/
def boundaryToWalls (n m : ℕ) (k : CellIndex n m) : C(Boundary n, walls n m) where
  toFun t := ⟨cell n m k t,⟨k,t,rfl⟩⟩
  continuous_toFun := by fun_prop

@[simp] theorem boundaryToWalls_val (n m : ℕ) (k : CellIndex n m) (t : Boundary n) :
    (boundaryToWalls n m k t).val = cell n m k t := rfl

/-- A point on the original outer cube boundary belongs to the actual grid
walls. This includes the genuinely empty boundary in dimension zero. -/
theorem boundary_subset_walls (n m : ℕ) : _root_.Cube.boundary (Fin n) ⊆ walls n m := by
  rintro x ⟨i,hi⟩
  obtain ⟨k,t,ht⟩ := cell_covers n m x
  have hd : (0 : ℝ) < m+1 := by positivity
  have he := congrArg (fun z : Cube n ↦ (z i : ℝ)) ht
  change ((k i : ℝ) + t i) / (m+1) = (x i : ℝ) at he
  have hti : t i = 0 ∨ t i = 1 := by
    rcases hi with hi | hi
    · have hx : (x i : ℝ) = 0 := congrArg (fun z : unitInterval ↦ (z : ℝ)) hi
      have hz : (k i : ℝ) + t i = 0 := by
        rw [hx] at he
        exact (div_eq_zero_iff).mp he |>.resolve_right hd.ne'
      left
      apply Subtype.ext
      change (t i : ℝ) = 0
      have hk : (0 : ℝ) ≤ k i := by positivity
      linarith [(t i).2.1]
    · have hx : (x i : ℝ) = 1 := congrArg (fun z : unitInterval ↦ (z : ℝ)) hi
      have hz : (k i : ℝ) + t i = m+1 := (div_eq_one_iff_eq hd.ne').mp (he.trans hx)
      right
      apply Subtype.ext
      change (t i : ℝ) = 1
      have hk : (k i : ℝ) ≤ m := by exact_mod_cast Nat.le_of_lt_succ (k i).isLt
      linarith [(t i).2.2]
  exact ⟨k,⟨t,⟨i,hti⟩⟩,ht⟩

/-- Exact cell fillers agreeing with the supplied wall map paste continuously
and retain that entire map. No extension over the walls is assumed implicitly. -/
theorem exists_paste_from_walls (n m : ℕ) {X : Type u} [TopologicalSpace X]
    (a : C(walls n m, X)) (f : ∀ _k : CellIndex n m, C(Cube n, X))
    (hf : ∀ k (t : Boundary n), f k t = a (boundaryToWalls n m k t)) :
    ∃ g : C(Cube n,X), (∀ k t, g (cell n m k t) = f k t) ∧
      ∀ x : walls n m, g x = a x := by
  have hcompat : ∀ k l s t, cell n m k s = cell n m l t → f k s = f l t := by
    intro k l s t h
    by_cases hkl : k = l
    · subst l
      rw [cell_injective n m k h]
    · obtain ⟨hs,ht⟩ := cell_intersection_boundary n m k l hkl s t h
      calc
        f k s = a (boundaryToWalls n m k ⟨s,hs⟩) := hf k ⟨s,hs⟩
        _ = a (boundaryToWalls n m l ⟨t,ht⟩) := congrArg a (Subtype.ext h)
        _ = f l t := (hf l ⟨t,ht⟩).symm
  obtain ⟨g,hg⟩ := exists_paste n m f hcompat
  refine ⟨g,hg,?_⟩
  intro x
  obtain ⟨k,t,ht⟩ := x.2
  have h := (hg k t).trans (hf k t)
  have he : boundaryToWalls n m k t = x := Subtype.ext ht
  simpa only [ht,he] using h

/-- Pasting actual lifts on cells gives a lift of the original whole-cube map,
with the prescribed grid-wall map unchanged. -/
theorem exists_lift_from_wall_cell_lifts (n m : ℕ)
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (b : C(Cube n, B)) (a : C(walls n m, E))
    (f : ∀ _k : CellIndex n m, C(Cube n,E))
    (hf : ∀ k (t : Boundary n), f k t = a (boundaryToWalls n m k t))
    (hp : ∀ k, p.comp (f k) = b.comp (cell n m k)) :
    ∃ g : C(Cube n,E), p.comp g = b ∧ ∀ x : walls n m, g x = a x := by
  obtain ⟨g,hg,ha⟩ := exists_paste_from_walls n m a f hf
  refine ⟨g,?_,ha⟩
  apply paste_unique n m
  intro k t
  change p (g (cell n m k t)) = b (cell n m k t)
  rw [hg]
  exact ContinuousMap.congr_fun (hp k) t

end Topology.CubicalSubdivision
