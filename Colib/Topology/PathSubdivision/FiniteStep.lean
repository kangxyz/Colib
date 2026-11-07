/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.PathSubdivision.TailMaps
public import Colib.Topology.PathSubdivision.PoolComparison

/-!
# One actual finite-subdivision step with moved parameters

Finite HELP is applied only to the actual cube, through the genuine two-chart
pool comparison. Its output parameter is allowed to move. Appending the
remaining original tail at that current parameter turns the entire pool
homotopy into a homotopy in the original pullback, fixed on the original
outer boundary. No lifting on an open parameter locus is selected.


Implementation provenance:
`Quillen/Topology/PathSubdivision/FiniteStep.lean`
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
variable {D E X B : Type u} [TopologicalSpace D] [TopologicalSpace E]
  [TopologicalSpace X] [TopologicalSpace B]

/-- Forgetting the entrance's chart witness retains exactly the original
affine segment, including its complete path. -/
theorem twoPoolForget_entrance_slab (p : C(E, B)) (H : C(unitInterval × D, B))
    (m : ℕ) (i : Fin (m + 1)) (U V : Set B)
    (hcover : ∀ d, slabMap H m i d ∈ pathSet U ∨ slabMap H m i d ∈ pathSet V) :
    (twoPoolForget p (slabMap H m i) U V).comp
      (twoPoolEntrance p (slabMap H m i) U V hcover) =
        stageSegment p H (intervalCell m i 0) (intervalCell m i 1) := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  refine Prod.ext rfl ?_
  refine Prod.ext rfl ?_
  apply ContinuousMap.ext
  intro r
  exact congrArg (fun t ↦ H (t,z.val.1)) (timePath_intervalCell m i r).symm

variable (p : C(E, B)) (H : C(unitInterval × D, B)) (n : ℕ)
  (a : C(boundary.{u} n, D)) (e : C(boundary.{u} n, E))
  (he : ∀ z, p (e z) = H (1, a z))
  (hfixed : ∀ t z, H (t, a z) = H (1, a z))

/-- The same original boundary parameter and source at every subdivision time. -/
def boundaryStage (s : unitInterval) : C(boundary.{u} n,Stage p H s) where
  toFun z := ⟨(a z,e z),(he z).trans (hfixed s z).symm⟩
  continuous_toFun := by fun_prop

@[simp] theorem boundaryStage_parameter (s : unitInterval) (z : boundary.{u} n) :
    (boundaryStage p H n a e he hfixed s z).val.1 = a z := rfl

@[simp] theorem boundaryStage_source (s : unitInterval) (z : boundary.{u} n) :
    (boundaryStage p H n a e he hfixed s z).val.2 = e z := rfl

variable (f : C(X, B)) (k : C(D, X)) (hEnd : ∀ d, H (1, d) = f (k d))

/-- A genuine weak comparison for one original two-chart slab advances a
finite cube lift, preserving its exact original boundary and a relative
homotopy in the final original homotopy pullback. -/
theorem exists_finite_slab_step (m : ℕ) (i : Fin (m + 1)) (U V : Set B)
    (hcover : ∀ d, slabMap H m i d ∈ pathSet U ∨ slabMap H m i d ∈ pathSet V)
    (hweak : IsWeakHomotopyEquivalence (twoPoolComparison p (slabMap H m i) U V hcover))
    (c : C(cube.{u} n, Stage p H (intervalCell m i 0)))
    (hc : c.comp (boundaryInclusion n).hom =
      boundaryStage p H n a e he hfixed (intervalCell m i 0)) :
    ∃ c' : C(cube.{u} n,Stage p H (intervalCell m i 1)),
      c'.comp (boundaryInclusion n).hom =
        boundaryStage p H n a e he hfixed (intervalCell m i 1) ∧
      Nonempty (((stageToPullback p f H k hEnd (intervalCell m i 1)).comp c').HomotopyRel
        ((stageToPullback p f H k hEnd (intervalCell m i 0)).comp c)
          (Set.range (boundaryInclusion n))) := by
  let s := intervalCell m i 0
  let t := intervalCell m i 1
  let γ := slabMap H m i
  let j := twoPoolComparison p γ U V hcover
  let enter := twoPoolEntrance p γ U V hcover
  let a' : C(boundary.{u} n,StrictPool p γ) := boundaryStage p H n a e he hfixed t
  let b' := enter.comp c
  have w : j.comp a' = b'.comp (boundaryInclusion n).hom := by
    rw [ContinuousMap.comp_assoc,hc]
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    apply Subtype.ext
    refine Prod.ext rfl ?_
    refine Prod.ext rfl ?_
    apply ContinuousMap.ext
    intro r
    exact (hfixed t z).trans (hfixed (intervalCell m i r) z).symm
  obtain ⟨c',hc',⟨K⟩⟩ := hweak.cube_strictHELP n a' b' w
  let append := appendToPullback p f H k hEnd t
  let forget := twoPoolForget p γ U V
  let L := K.compContinuousMap (append.comp forget)
  have hL : Nonempty (((append.comp (HomotopyPullback.strictPullbackInclusion p (slice H
    t))).comp c').HomotopyRel
      ((append.comp (stageSegment p H s t)).comp c) (Set.range (boundaryInclusion n))) := by
    refine ⟨L.cast rfl ?_⟩
    change (append.comp forget).comp (enter.comp c) = _
    apply ContinuousMap.ext
    intro x
    exact congrArg append (ContinuousMap.congr_fun
      (twoPoolForget_entrance_slab p H m i U V hcover) (c x))
  obtain ⟨L'⟩ := hL
  let R₁ : (((stageToPullback p f H k hEnd t).comp c')).HomotopyRel
      ((append.comp (HomotopyPullback.strictPullbackInclusion p (slice H t))).comp c')
        (Set.range (boundaryInclusion n)) := {
    toHomotopy := ((stageUnpadHomotopy p f H k hEnd t).compContinuousMap c').symm
    prop' := by
      rintro r _ ⟨z,rfl⟩
      apply stageUnpadHomotopy_fixed p f H k hEnd t
      intro q
      change H (q,(c' ((boundaryInclusion n) z)).val.1) =
        H (1,(c' ((boundaryInclusion n) z)).val.1)
      rw [show c' ((boundaryInclusion n) z) = boundaryStage p H n a e he hfixed t z from
        ContinuousMap.congr_fun hc' z]
      exact hfixed q z }
  let R₂ : (((append.comp (stageSegment p H s t)).comp c)).HomotopyRel
      ((stageToPullback p f H k hEnd s).comp c) (Set.range (boundaryInclusion n)) := {
    toHomotopy := (stageJoinHomotopy p f H k hEnd s t).compContinuousMap c
    prop' := by
      rintro r _ ⟨z,rfl⟩
      have hconst : ∀ q,H (q,(c ((boundaryInclusion n) z)).val.1) =
          H (1,(c ((boundaryInclusion n) z)).val.1) := by
        have hz : c ((boundaryInclusion n) z) = boundaryStage p H n a e he hfixed s z :=
          ContinuousMap.congr_fun hc z
        rw [hz]
        exact fun q ↦ hfixed q z
      exact (stageJoinHomotopy_fixed p f H k hEnd s t _ hconst r).trans
        ((stageJoinHomotopy_fixed p f H k hEnd s t _ hconst 0).symm.trans
          ((stageJoinHomotopy p f H k hEnd s t).map_zero_left _)) }
  exact ⟨c',hc',⟨R₁.trans (L'.trans R₂)⟩⟩

end Topology.PathSubdivision
