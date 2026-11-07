/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.Topology.LocalCoefficients.SimplexAttachmentExcision

/-! # The original twisted small-chain, open-excision, and attachment maps -/

open CategoryTheory Limits FundamentalGroupoid.LocalCoefficients
open Convexity.StdSimplex TopCat
open scoped Simplicial

universe u v

noncomputable section

example {X : Type u} [TopologicalSpace X] (A : System.{u, u} X) :
    Homotopy (𝟙 (singularChainComplex A)) (barycentricSubdivision A) :=
  barycentricSubdivisionHomotopy A

example {X : Type u} [TopologicalSpace X] {ι : Type v} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i) (A : System.{u, u} X) :
    QuasiIso (smallChainComplexInclusion U A) :=
  smallChainComplexInclusion_quasiIso U hU hcover A

example {X : Type u} [TopologicalSpace X] (U V : Set X) (A : System.{u, u} X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    QuasiIso (relativePushforwardChainMap (subspaceInclusion U)
      (intersectionInSubspace U V) V (fun _ h ↦ h)
      A) :=
  relativePushforwardChainMap_openExcision U V A hU hV hcover

example (X : TopCat.{u}) {B D : TopCat.{u}}
    {f : TopCat.of (X × boundary 0) ⟶ B}
    {g : TopCat.of (X × Convexity.StdSimplex ℝ (Fin 1)) ⟶ D} {j : B ⟶ D}
    (sq : IsPushout (parameterizedSimplexBoundaryInclusion X 0) f g j)
    (A : System.{u, u} D) :
    QuasiIso (relativePushforwardChainMap g.hom (SimplexAttachment.sourceBoundary X 0)
      (SimplexAttachment.baseImage (j := j))
      (SimplexAttachment.cell_mapsTo_boundary X 0 sq) A) :=
  simplexAttachmentCell_relative_quasiIso X 0 sq A
