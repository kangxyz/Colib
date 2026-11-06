/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Homotopy.HomotopyGroup.CompactLifting
public import Colib.Topology.HomotopyFiber.SourceEquivalence
public import Colib.Topology.Homotopy.Equiv.AdjacentComposites

/-! # Exact compact-source lifting is retained on actual homotopy fibers

For a prescribed injective continuous source map, lift only the source
coordinate of a compact family of actual homotopy-fiber points and retain
its original path coordinate. The exact source-lifting equation verifies
both path endpoints. This provides actual finite homotopy-set bijections,
including degree zero, with no Whitehead or fiber-equivalence hypothesis.


Implementation provenance:
`Quillen/Topology/HomotopyFiber/CompactLifting.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section


noncomputable section
open scoped Topology
universe u v w

namespace Topology.HomotopyFiber
variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Injectivity of the original source map retains the complete source/path
pair in every actual homotopy fiber. -/
theorem sourceMap_injective (f : C(Y, Z)) (e : C(X, Y)) (he : Function.Injective e) (z : Z) :
    Function.Injective (sourceMap f e z) := by
  intro a b h
  apply Subtype.ext
  apply _root_.Prod.ext
  · exact he (congrArg (fun q : HomotopyFiber f z ↦ q.1.1) h)
  · exact congrArg (fun q : HomotopyFiber f z ↦ q.1.2) h

/-- Compact-source lifting preserves the original path coordinate, and hence
lifts actual homotopy fibers exactly rather than only up to homotopy. -/
theorem sourceMap_compact_lifts (f : C(Y, Z)) (e : C(X, Y))
    (hl : HasCompactSourceLifts e) (z : Z) : HasCompactSourceLifts (sourceMap f e z) := by
  intro T _ _ g
  obtain ⟨h, hh⟩ := hl T ((projection f z).comp g)
  let k : C(T, HomotopyFiber (f.comp e) z) := {
    toFun t := ⟨(h t, (g t).1.2),
      (g t).2.1.trans (congrArg f (DFunLike.congr_fun hh t)).symm, (g t).2.2⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.prodMk
      · exact h.continuous
      · fun_prop }
  refine ⟨k, ?_⟩
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  exact _root_.Prod.ext (DFunLike.congr_fun hh t) rfl

/-- Every finite based homotopy set sees exactly the canonical source map
on the original actual homotopy fibers. -/
theorem sourceMap_homotopyGroupMap_bijective (f : C(Y, Z)) (e : C(X, Y))
    (he : Function.Injective e) (hl : HasCompactSourceLifts e) (z : Z)
    (x : HomotopyFiber (f.comp e) z) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) (sourceMap f e z) (x := x) rfl) :=
  homotopyGroupMap_bijective_of_compact_lifts (sourceMap f e z)
    (sourceMap_injective f e he z) (sourceMap_compact_lifts f e hl z) x n

end Topology.HomotopyFiber
