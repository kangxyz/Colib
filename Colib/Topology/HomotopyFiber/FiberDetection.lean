/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.GroupDetection
public import Colib.Topology.Homotopy.HomotopyGroup.ZeroDetection
public import Colib.Topology.Homotopy.FreePath
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransport

/-! # All-degree fiber detection over a common base

The positive-degree argument is the actual long exact sequence. Genuine
path connectedness handles dimension zero and transports the resulting
bijections to every source point. No inverse family is selected.


Implementation provenance:
`Quillen/Topology/HomotopyFiber/FiberDetection.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w

namespace Topology.HomotopyFiber
variable {X : Type u} {Y : Type v} {B : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace B]
  (f : C(X, B)) (g : C(Y, B)) (u : C(X, Y)) (sq : g.comp u = f)
  (x : X) (b : B) (hx : f x = b)

/-- Actual fiber maps at the chosen point detect every finite homotopy-set
bijection of a map over one base, including dimension zero. -/
theorem homotopyGroupMap_bijective_of_fiberMap
    [PathConnectedSpace X] [PathConnectedSpace Y]
    (h : ∀ n : ℕ, Function.Bijective (HomotopyGroup.map (N := Fin n)
      (mapOver f g u sq b) (mapOver_basepoint f g u sq x b hx))) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) u (x := x) rfl) := by
  cases n with
  | zero => exact homotopyGroupMap_zero_bijective u x
  | succ n => exact piMap_bijective_of_fiberMap f g u sq x b hx n (h (n + 1)) (h n).injective

/-- The same original map is bijective at every source point, by proved
path transport rather than an assumed continuous inverse family. -/
theorem homotopyGroupMap_bijective_at_all_points_of_fiberMap
    [PathConnectedSpace X] [PathConnectedSpace Y]
    (h : ∀ n : ℕ, Function.Bijective (HomotopyGroup.map (N := Fin n)
      (mapOver f g u sq b) (mapOver_basepoint f g u sq x b hx))) (x' : X) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) u (x := x') rfl) := by
  exact (homotopyGroupMap_bijective_iff_of_joined u (PathConnectedSpace.joined x x') n).1
    (homotopyGroupMap_bijective_of_fiberMap f g u sq x b hx h n)

end Topology.HomotopyFiber
