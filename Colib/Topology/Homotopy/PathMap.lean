/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Mathlib.Topology.Homotopy.Path

/-!
# Path Map

Transport an actual relative path homotopy through an exact continuous-map
composition identity. The whole square is unchanged, not just its endpoints.
-/

@[expose] public section

noncomputable section
universe u v w
namespace Path
variable {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Transport an actual relative path homotopy through an exact continuous-map
composition identity. The whole square is unchanged, not just its endpoints. -/
def homotopyMapCompOfEq (i : C(X, Y)) (j : C(Y, Z)) (k : C(X, Z))
    (h : j.comp i = k) {x y : X} (p q : Path x y)
    (H : (p.map k.continuous).Homotopy (q.map k.continuous)) :
    ((p.map i.continuous).map j.continuous).Homotopy
      ((q.map i.continuous).map j.continuous) where
  toFun := H
  continuous_toFun := H.continuous
  map_zero_left t := (H.map_zero_left t).trans
    (congrArg (fun f : C(X, Z) => f (p t)) h).symm
  map_one_left t := (H.map_one_left t).trans
    (congrArg (fun f : C(X, Z) => f (q t)) h).symm
  prop' t z hz := (H.prop' t z hz).trans
    (congrArg (fun f : C(X, Z) => f (p z)) h).symm

/-- The same exact transport on relative-homotopy existence. -/
theorem homotopic_map_comp_of_eq (i : C(X, Y)) (j : C(Y, Z)) (k : C(X, Z))
    (h : j.comp i = k) {x y : X} (p q : Path x y)
    (H : (p.map k.continuous).Homotopic (q.map k.continuous)) :
    ((p.map i.continuous).map j.continuous).Homotopic
      ((q.map i.continuous).map j.continuous) := by
  obtain ⟨H⟩ := H
  exact ⟨homotopyMapCompOfEq i j k h p q H⟩

end Path
