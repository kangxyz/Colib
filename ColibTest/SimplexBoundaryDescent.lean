/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.Topology.Realization.SimplexBoundary.SimplyConnected
public import Colib.Topology.Realization.SimplexBoundary.TriangleRelation

@[expose] public noncomputable section
open CategoryTheory Convexity Convexity.StdSimplex
open Convexity.StdSimplex.Boundary
universe u v

example (n : ℕ) (i : Fin (n + 3)) : ContractibleSpace (vertexStar i) :=
  contractible_vertexStar i

example (n : ℕ) (i j : Fin (n + 3)) : ContractibleSpace ↥(vertexStar i ∩ vertexStar j) :=
  contractible_overlap i j

example {C : Type u} [Groupoid.{v} C]
    (F : FundamentalGroupoid (simplexBoundary 2) ⥤ C)
    (h : edgeMap F 0 1 ≫ edgeMap F 1 2 = edgeMap F 0 2) :
    F ≅ (Functor.const (FundamentalGroupoid (simplexBoundary 2))).obj
      (F.obj (FundamentalGroupoid.mk (vertex 0))) :=
  boundaryConstantIsoOfTriangle F h

example {C : Type u} [Groupoid.{v} C] (n : ℕ)
    (F : FundamentalGroupoid (simplexBoundary (n + 3)) ⥤ C) :
    F ≅ (Functor.const (FundamentalGroupoid (simplexBoundary (n + 3)))).obj
      (F.obj (FundamentalGroupoid.mk (vertex 0))) :=
  boundaryConstantIso F

example (n : ℕ) (hn : 3 ≤ n) : IsSimplyConnected (simplexBoundary n) :=
  isSimplyConnected_simplexBoundary hn

example : IsSimplyConnected (simplexBoundary 3) :=
  isSimplyConnected_simplexBoundary (by decide)
