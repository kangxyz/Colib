/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Analysis.Convex.StdSimplex.PathHomotopy
public import Mathlib.Analysis.Convex.StdSimplex

/-!
# Prescribed interpolation of the two boundary routes of a continuous square

Coordinatewise standard-simplex interpolation gives an explicit endpoint-relative comparison
of the two original boundary routes. Composing with a displayed continuous square retains its
whole image; no path-homotopy existence witness is selected. The cofiber-prism boundary uses
this construction in its actual based-loop space.
-/
/-! Adapted from `Quillen/Topology/Homotopy/SquareBoundaryPaths.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual paths and coordinates. -/
@[expose] public section
noncomputable section
open scoped Topology unitInterval
universe u
namespace Topology

/-- Coordinatewise standard-simplex interpolation of paths in the original parameter square. -/
def unitSquarePathHomotopy {x y : unitInterval × unitInterval} (p q : Path x y) :
    p.Homotopy q := by
  let intervalHomotopy {a b : unitInterval} (α β : Path a b) : α.Homotopy β := by
    let e := stdSimplexHomeomorphUnitInterval.symm
    let H := (stdSimplex.pathHomotopy (α.map e.continuous)
      (β.map e.continuous)).map ⟨e.symm, e.symm.continuous⟩
    let H' := H.pathCast (e.symm_apply_apply a).symm (e.symm_apply_apply b).symm
    refine H'.cast ?_ ?_ <;> apply Path.ext <;> funext t <;> exact e.symm_apply_apply _
  let H₁ := intervalHomotopy (p.map continuous_fst) (q.map continuous_fst)
  let H₂ := intervalHomotopy (p.map continuous_snd) (q.map continuous_snd)
  exact {
    toFun z := (H₁ z, H₂ z)
    continuous_toFun := by fun_prop
    map_zero_left t := Prod.ext (H₁.apply_zero t) (H₂.apply_zero t)
    map_one_left t := Prod.ext (H₁.apply_one t) (H₂.apply_one t)
    prop' s t ht := Prod.ext (ContinuousMap.HomotopyRel.eq_fst H₁ s ht)
      (ContinuousMap.HomotopyRel.eq_fst H₂ s ht) }

/-- The left-then-top boundary route and bottom-then-right route keep their original edges. -/
def squareBoundaryPathHomotopy {X : Type u} [TopologicalSpace X]
    (F : C(unitInterval × unitInterval, X)) :
    (((Path.refl (0 : unitInterval)).prod Path.id).map F.continuous |>.trans
      ((Path.id.prod (Path.refl (1 : unitInterval))).map F.continuous)).Homotopy
      (((Path.id.prod (Path.refl (0 : unitInterval))).map F.continuous).trans
        (((Path.refl (1 : unitInterval)).prod Path.id).map F.continuous)) := by
  let p := ((Path.refl (0 : unitInterval)).prod Path.id).trans
    (Path.id.prod (Path.refl (1 : unitInterval)))
  let q := (Path.id.prod (Path.refl (0 : unitInterval))).trans
    ((Path.refl (1 : unitInterval)).prod Path.id)
  exact ((unitSquarePathHomotopy p q).map F).cast
    (Path.map_trans _ _ _) (Path.map_trans _ _ _)

end Topology
