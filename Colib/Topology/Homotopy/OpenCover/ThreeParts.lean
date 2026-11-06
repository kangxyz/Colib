/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Mathlib.Topology.Subpath

/-!
# Three Parts

First subpath with its source transported to the original actual endpoint.
-/

@[expose] public section

noncomputable section
open Set CategoryTheory
universe u
namespace FundamentalGroupoid.OpenCover
variable {X : Type u} [TopologicalSpace X] {x y : X}

/-- First subpath with its source transported to the original actual endpoint. -/
def firstPart (p : Path x y) (a : unitInterval) : Path x (p a) :=
  (p.subpath 0 a).cast p.source.symm rfl
/-- Last subpath with its target transported to the original actual endpoint. -/
def lastPart (p : Path x y) (b : unitInterval) : Path (p b) y :=
  (p.subpath b 1).cast rfl p.target.symm

/-- The actual three-part concatenation is endpoint-fixed homotopic to the
original path, with the exact original endpoints rather than parameter labels. -/
def threePartHomotopy (p : Path x y) (a b : unitInterval) :
    ((firstPart p a).trans ((p.subpath a b).trans (lastPart p b))).Homotopy p := by
  let H := ((Path.Homotopy.refl (p.subpath 0 a)).hcomp
    (Path.Homotopy.subpathTransSubpath p a b 1)).trans
      (Path.Homotopy.subpathTransSubpath p 0 a 1)
  refine (H.pathCast p.source.symm p.target.symm).cast ?_ ?_
  · rfl
  · ext t
    change p (Icc.convexComb 0 1 t) = p t
    simp

end FundamentalGroupoid.OpenCover
