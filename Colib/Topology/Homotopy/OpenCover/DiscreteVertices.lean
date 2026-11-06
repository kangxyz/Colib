/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Discrete Vertices

An actual path class in a totally disconnected vertex space has equal endpoints.
-/

@[expose] public section

noncomputable section
open CategoryTheory
universe u v w
namespace FundamentalGroupoid.OpenCover
variable {X : Type u} [TopologicalSpace X] [TotallyDisconnectedSpace X]
variable {C : Type v} [Category.{w} C]

/-- An actual path class in a totally disconnected vertex space has equal endpoints. -/
theorem vertexEndpoints_eq {x y : X} (f : Path.Homotopic.Quotient x y) : x = y := by
  induction f using _root_.Quotient.ind with | _ p =>
    have h := TotallyDisconnectedSpace.eq_of_continuous p p.continuous 0 1
    simpa using h

/-- Decode the discrete zero-skeleton by any specified vertex object assignment.
The map on every actual path class is exactly its endpoint equality transport. -/
def discreteVertexFunctor (obj : X → C) : FundamentalGroupoid X ⥤ C where
  obj x := obj x.as
  map f := eqToHom (congrArg obj (vertexEndpoints_eq f))
  map_id _ := by simp
  map_comp _ _ := by simp

/-- The actual zero-skeleton decoder has its prescribed vertex objects literally. -/
theorem discreteVertexFunctor_obj (obj : X → C) (x : X) :
    (discreteVertexFunctor obj).obj (FundamentalGroupoid.mk x) = obj x := rfl

end FundamentalGroupoid.OpenCover
