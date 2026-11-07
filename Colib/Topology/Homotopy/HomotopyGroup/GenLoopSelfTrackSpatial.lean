/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.Loop.NormalizedSelfTrackNaturality

/-!
# Spatial coordinates of actual normalized self-tracks

Concatenation is the original generalized-loop concatenation. The normalization
changes only the first original cube coordinate and the separate track time.
The evaluation lemma below makes this dependence explicit before any quotient
or group-law argument.
-/
/-! Implementation source: `Quillen/Topology/HomotopyGroups/GenLoopSelfTrackSpatial.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original cube coordinates,
whole tracks and group laws are retained under native Colib ownership. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u v
namespace Topology

/-- Restoring a split cube with a new displayed coordinate is the literal coordinate update. -/
theorem cube_insertAt_splitAt {N : Type v} [DecidableEq N] (i : N)
    (z : N → unitInterval) (s : unitInterval) :
    Cube.insertAt i (s, (Cube.splitAt i z).2) = Function.update z i s := by
  funext j
  simp only [Homeomorph.funSplitAt_symm_apply, Homeomorph.funSplitAt_apply,
    Function.update, eq_rec_constant, dite_eq_ite]

/-- Original spatial concatenation is jointly continuous in its two original cubes. -/
def genLoopTransAtContinuousMap {N : Type v} [DecidableEq N]
    {X : Type u} [TopologicalSpace X] {x : X} (i : N) :
    C(GenLoop N X x × GenLoop N X x, GenLoop N X x) where
  toFun z := GenLoop.transAt i z.1 z.2
  continuous_toFun := by
    have h : Continuous (fun z : GenLoop N X x × GenLoop N X x ↦
        GenLoop.fromLoop i ((GenLoop.toLoop i z.1).trans (GenLoop.toLoop i z.2))) :=
      (GenLoop.continuous_fromLoop i).comp (Path.continuous_trans.comp
        (((GenLoop.continuous_toLoop i).comp continuous_fst).prodMk
          ((GenLoop.continuous_toLoop i).comp continuous_snd)))
    exact h.congr (fun _ ↦ GenLoop.fromLoop_trans_toLoop)

/-- Concatenate the actual self-tracks in a displayed spatial coordinate at every track time. -/
def genLoopTransAtPath {N : Type v} [DecidableEq N]
    {X : Type u} [TopologicalSpace X] {x : X} (i : N)
    {p q : GenLoop N X x} (α : Path p p) (β : Path q q) :
    Path (GenLoop.transAt i p q) (GenLoop.transAt i p q) :=
  (α.prod β).map (genLoopTransAtContinuousMap i).continuous

/-- Spatial concatenation preserves the original independent track time. -/
@[simp] theorem genLoopTransAtPath_apply {N : Type v} [DecidableEq N]
    {X : Type u} [TopologicalSpace X] {x : X} (i : N)
    {p q : GenLoop N X x} (α : Path p p) (β : Path q q)
    (t : unitInterval) (z : N → unitInterval) :
    genLoopTransAtPath i α β t z = GenLoop.transAt i (α t) (β t) z := rfl

/-- Normalization at fixed residual coordinates only reads the original first-coordinate lines. -/
theorem genLoopNormalizedSelfTrackPath_congr_eval
    {X : Type u} [TopologicalSpace X] {x : X} (m : ℕ)
    (p q : GenLoop (Fin (m + 1)) X x) (α : Path p p) (β : Path q q)
    (z w : Fin (m + 1) → unitInterval) (h₀ : z 0 = w 0)
    (hp : ∀ s, p (Function.update z 0 s) = q (Function.update w 0 s))
    (hα : ∀ t s, α t (Function.update z 0 s) = β t (Function.update w 0 s))
    (t : unitInterval) :
    genLoopNormalizedSelfTrackPath m p α t z =
      genLoopNormalizedSelfTrackPath m q β t w := by
  let L := GenLoop.loopHomeo (X := X) (x := x) (0 : Fin (m + 1))
  change (loopNormalizedSelfTrack (L.toHomotopyEquiv.toFun p)
      (α.map L.toHomotopyEquiv.toFun.continuous) t (z 0)) ((Cube.splitAt 0 z).2) =
    (loopNormalizedSelfTrack (L.toHomotopyEquiv.toFun q)
      (β.map L.toHomotopyEquiv.toFun.continuous) t (w 0)) ((Cube.splitAt 0 w).2)
  rw [← h₀]
  refine loopNormalizedSelfTrack_pointwise
    (fun r : GenLoop {j : Fin (m + 1) // j ≠ 0} X x ↦ r ((Cube.splitAt 0 z).2))
    (fun r : GenLoop {j : Fin (m + 1) // j ≠ 0} X x ↦ r ((Cube.splitAt 0 w).2))
    (L.toHomotopyEquiv.toFun p) (L.toHomotopyEquiv.toFun q)
    (α.map L.toHomotopyEquiv.toFun.continuous)
    (β.map L.toHomotopyEquiv.toFun.continuous) ?_ ?_ t (z 0)
  · intro s
    change p (Cube.insertAt 0 (s, (Cube.splitAt 0 z).2)) =
      q (Cube.insertAt 0 (s, (Cube.splitAt 0 w).2))
    simpa only [cube_insertAt_splitAt] using hp s
  · intro r s
    change α r (Cube.insertAt 0 (s, (Cube.splitAt 0 z).2)) =
      β r (Cube.insertAt 0 (s, (Cube.splitAt 0 w).2))
    simpa only [cube_insertAt_splitAt] using hα r s

end Topology
