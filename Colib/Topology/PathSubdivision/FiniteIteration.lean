/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.PathSubdivision.FiniteStep
public import Colib.Topology.CubicalSubdivision.FaceComplex

/-!
# Finite iteration through the literal uniform time mesh

Each step uses the actual two-chart path-pool comparison supplied for that
slab. The induction preserves the original boundary parameter and source,
and composes relative homotopies in the unchanged final homotopy pullback.
No continuous inverse or lifting property of a whole path space is assumed.


Implementation provenance:
`Quillen/Topology/PathSubdivision/FiniteIteration.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open Topology.CubicalSubdivision
open Topology.CubicalTests


noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u
namespace Topology.PathSubdivision
open CubicalSubdivision CubicalTests

/-- The time mesh starts at literal zero. -/
theorem gridVertex_first (m : ℕ) : gridVertex m ⟨0,by omega⟩ = 0 := by
  apply Subtype.ext
  simp [gridVertex]

/-- The time mesh ends at literal one. -/
theorem gridVertex_last (m : ℕ) : gridVertex m ⟨m+1,by omega⟩ = 1 := by
  apply Subtype.ext
  change (((m+1 : ℕ) : ℝ)/(m+1)) = 1
  rw [Nat.cast_add,Nat.cast_one]
  exact div_self (by positivity)

/-- Every actual slab starts at its original mesh vertex. -/
theorem intervalCell_zero_vertex (m : ℕ) (i : Fin (m + 1)) :
    intervalCell m i 0 = gridVertex m i.castSucc := by
  apply Subtype.ext
  simp [intervalCell,gridVertex]

/-- Every actual slab ends at the next original mesh vertex. -/
theorem intervalCell_one_vertex (m : ℕ) (i : Fin (m + 1)) :
    intervalCell m i 1 = gridVertex m i.succ := by
  apply Subtype.ext
  simp [intervalCell,gridVertex]

variable {D E X B : Type u} [TopologicalSpace D] [TopologicalSpace E]
  [TopologicalSpace X] [TopologicalSpace B]
  (p : C(E, B)) (H : C(unitInterval × D, B)) (n : ℕ)
  (a : C(boundary.{u} n, D)) (e : C(boundary.{u} n, E))
  (he : ∀ z, p (e z) = H (1, a z))
  (hfixed : ∀ t z, H (t, a z) = H (1, a z))
  (f : C(X, B)) (k : C(D, X)) (hEnd : ∀ d, H (1, d) = f (k d))

/-- Advance the complete original cube across all finitely many actual slabs.
The supplied weak inputs concern the genuine local path pools only. -/
theorem exists_finite_time_lift (m : ℕ) (U V : Set B)
    (hcover : ∀ (i : Fin (m + 1)) d,
      slabMap H m i d ∈ pathSet U ∨ slabMap H m i d ∈ pathSet V)
    (hweak : ∀ i : Fin (m+1),IsWeakHomotopyEquivalence
      (twoPoolComparison p (slabMap H m i) U V (hcover i)))
    (c₀ : C(cube.{u} n,Stage p H 0))
    (hc₀ : c₀.comp (boundaryInclusion n).hom = boundaryStage p H n a e he hfixed 0) :
    ∃ c₁ : C(cube.{u} n,Stage p H 1),
      c₁.comp (boundaryInclusion n).hom = boundaryStage p H n a e he hfixed 1 ∧
      Nonempty (((stageToPullback p f H k hEnd 1).comp c₁).HomotopyRel
        ((stageToPullback p f H k hEnd 0).comp c₀) (Set.range (boundaryInclusion n))) := by
  let P : unitInterval → Prop := fun s ↦
    ∃ c : C(cube.{u} n,Stage p H s),
      c.comp (boundaryInclusion n).hom = boundaryStage p H n a e he hfixed s ∧
      Nonempty (((stageToPullback p f H k hEnd s).comp c).HomotopyRel
        ((stageToPullback p f H k hEnd 0).comp c₀) (Set.range (boundaryInclusion n)))
  have hstep (i : Fin (m+1)) : P (intervalCell m i 0) → P (intervalCell m i 1) := by
    rintro ⟨c,hc,⟨J⟩⟩
    obtain ⟨c',hc',⟨K⟩⟩ := exists_finite_slab_step p H n a e he hfixed f k hEnd
      m i U V (hcover i) (hweak i) c hc
    exact ⟨c',hc',⟨K.trans J⟩⟩
  have stages : ∀ (r : ℕ) (hr : r ≤ m+1),P (gridVertex m ⟨r,by omega⟩) := by
    intro r
    induction r with
    | zero =>
      intro hr
      rw [gridVertex_first]
      exact ⟨c₀,hc₀,⟨ContinuousMap.HomotopyRel.refl _ _⟩⟩
    | succ r ih =>
      intro hr
      let i : Fin (m+1) := ⟨r,by omega⟩
      have step := hstep i
      rw [intervalCell_zero_vertex,intervalCell_one_vertex] at step
      exact step (ih (by omega))
  have result := stages (m+1) le_rfl
  rw [gridVertex_last] at result
  exact result

end Topology.PathSubdivision
