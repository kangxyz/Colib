/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.SphericalSimplexQuotient
public import Colib.Topology.Homotopy.HomotopyGroup.Map

/-!
# Original-map naturality of spherical singular-simplex classes

Postcomposition retains the actual continuous map and the specified equality
of basepoints. The chosen simplex-to-cube class map commutes with the existing
HomotopyGroup.map by a literal equality on representatives.
-/

/-! Implementation source: `Quillen/Topology/HomotopyGroups/SphericalSimplexMap.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Native simplex coordinates,
original maps, endpoint paths, coefficient universe and chain signs are retained.
The spherical representatives use the explicit ordered stick-breaking quotient.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open Topology
universe u v

namespace Topology.SphericalSimplex
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {x : X} {y : Y} {n : ℕ}

/-- Postcompose an actual spherical simplex by a based continuous map. -/
def map (f : C(X, Y)) (h : f x = y) (σ : SphericalSimplex X x n) :
    SphericalSimplex Y y n :=
  ⟨f.comp σ.val, fun t ht ↦ (congrArg f (σ.boundary t ht)).trans h⟩

@[simp] theorem map_apply (f : C(X, Y)) (h : f x = y)
    (σ : SphericalSimplex X x n) (t : _root_.stdSimplex ℝ (Fin (n + 1))) :
    map f h σ t = f (σ t) := rfl

/-- The representative in the original cube model commutes with postcomposition. -/
@[simp] theorem toGenLoopStick_map (f : C(X, Y)) (h : f x = y)
    (σ : SphericalSimplex X x n) :
    (map f h σ).toGenLoopStick = GenLoop.postcomp f h σ.toGenLoopStick := rfl

/-- The class equation uses the original homotopy map, including its endpoint equality. -/
@[simp] theorem homotopyClassStick_map (f : C(X, Y)) (h : f x = y)
    (σ : SphericalSimplex X x n) :
    (map f h σ).homotopyClassStick = HomotopyGroup.map f h σ.homotopyClassStick := rfl

end Topology.SphericalSimplex
