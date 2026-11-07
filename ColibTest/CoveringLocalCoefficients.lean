/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Colib.Topology.LocalCoefficients.PullbackCoveringHomologyUniverseLift

/-! Native covering-fiber comparisons preserve the literal maps and coefficient universe. -/

open CategoryTheory FundamentalGroupoid.LocalCoefficients
open scoped Simplicial

universe u v

noncomputable section

example {X : Type u} [TopologicalSpace X] (A : System.{u, u} X)
    (σ : SingularSimplex X ⦋2⦌) :
    restrictionTransport A σ (SimplexCategory.δ 0) ≫
        eqToHom (congrArg (fiber A) (restrictSimplex_firstFace_vertex σ)) =
      simplexTransport A σ (stdSimplex.vertex 0) (stdSimplex.vertex 1) :=
  restrictionTransport_firstFace A σ

example {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    {q : E → B} (hq : IsCoveringMap q) (s : IsCoveringMap.BasedSimplex q ⦋2⦌) :
    (hq.restrict s (SimplexCategory.δ 0)).2.1 =
      (hq.simplexTransport s.1 (stdSimplex.vertex 0) (stdSimplex.vertex 1) s.2).1 :=
  hq.restrict_firstFace_point s

example {X : Type u} {B E : Type (u + 1)}
    [TopologicalSpace X] [TopologicalSpace B] [TopologicalSpace E]
    (f : C(X, B)) {q : E → B} (hq : IsCoveringMap q) :
    Arrow.mk (UniverseLift.homologyMap.{u, u + 1, u + 1} f
      (PullbackCovering.fiberSystem hq) 2) ≅
      Arrow.mk (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u + 1} ℤ) 2).obj
        (ModuleCat.of ℤ (ULift.{u + 1} ℤ))).map
          (TopCat.ofHom (Topology.Covering.Pullback.lift f q))) :=
  PullbackCoveringUniverseLift.successorHomologyTwoArrowIso f hq
