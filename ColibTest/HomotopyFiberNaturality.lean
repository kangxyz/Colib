/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.Topology.Homotopy.HomotopyGroup.PathComponentPositiveNaturality
import Colib.Topology.HomotopyFiber.HomotopyPiOneNaturality
import Colib.Topology.HomotopyFiber.LoopComparisonNaturality

/-!
# Actual component tracks and homotopy-fiber naturality

These tests retain the supplied component track, the original strict fiber map,
and the native positive homotopy-group homomorphisms in different universes.
-/

noncomputable section
universe u v w
open Topology Topology.HomotopyFiber

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

example (f : C(X, Y)) (x : X) (y : Y) (p : Path (f x) y) (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (pathComponent x) ⟨x, mem_pathComponent_self x⟩) :
    pathComponentPiMulEquiv y n
      (pathTransportMulEquiv (pathComponentMapBasepointPath f x y p) n
        (HomotopyGroup.piMap n (pathComponentMap f x y ⟨p⟩) rfl a)) =
      pathTransportMulEquiv p n
        (HomotopyGroup.piMap n f rfl (pathComponentPiMulEquiv x n a)) :=
  pathComponentPiMulEquiv_naturality_apply f x y p n a

example (p : C(X, Y)) (q : C(X, Z)) (v : C(Y, Z))
    (sq : v.comp p = q.comp (ContinuousMap.id X))
    (x : X) (y : Y) (h : p x = y) (z : Z) (hv : v y = z) (hq : q x = z)
    (h1 : Function.Injective (HomotopyGroup.piMap 0 v hv))
    (h2 : Function.Bijective (HomotopyGroup.piMap 1 v hv)) :
    Function.Bijective (HomotopyGroup.piMap 0 (mapAt (ContinuousMap.id X) v sq y z hv)
      (mapAt_basepoint (ContinuousMap.id X) v sq x y x z h hq rfl hv)) :=
  mapAt_piOne_bijective p q v sq x y h z hv hq h1 h2
