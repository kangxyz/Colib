/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.ClassifyingSpace.NerveCompletion.FaceTraces

/-!
# Nerve Triangle

The previously explicit triangle hypothesis for the ACTUAL nerve attaching
functor is discharged by the three original face traces and original composition.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Convexity.StdSimplex FundamentalGroupoid.OpenCover
universe u v
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover TopCat.SimplexAttachment Convexity.StdSimplex.Boundary
attribute [local instance] Localization.groupoid

/-- The previously explicit triangle hypothesis for the ACTUAL nerve attaching
functor is discharged by the three original face traces and original composition. -/
theorem nerveTwoCell_triangle (C : Type u) [Category.{v} C] (a : NerveTwoCellIndex C) :
    edgeMap (nerveTwoCellBoundaryFunctor C a) 0 1 ≫
        edgeMap (nerveTwoCellBoundaryFunctor C a) 1 2 =
      edgeMap (nerveTwoCellBoundaryFunctor C a) 0 2 := by
  rw [nerveTwoCell_trace_01, nerveTwoCell_trace_12, nerveTwoCell_trace_02]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp_assoc, ← a.simplex.map'_comp 0 1 2]

/-- A constructed constant natural isomorphism for each actual original two-cell
boundary attaching functor; no loop-killing or triangle hypothesis is assumed. -/
def nerveTwoCellBoundaryConstantIso (C : Type u) [Category.{v} C]
    (a : NerveTwoCellIndex C) :
    nerveTwoCellBoundaryFunctor C a ≅
      (Functor.const (FundamentalGroupoid (Convexity.StdSimplex.boundary 2))).obj
        ((nerveTwoCellBoundaryFunctor C a).obj (FundamentalGroupoid.mk (vertex 0))) :=
  boundaryConstantIsoOfTriangle _ (nerveTwoCell_triangle C a)

/-- Every actual original two-cell boundary loop is killed by the actual graph
decoder after the original attaching map, including cells with degenerate faces. -/
theorem nerveTwoCell_boundary_loop (C : Type u) [Category.{v} C]
    (a : NerveTwoCellIndex C) (x : Convexity.StdSimplex.boundary 2) (p : Path x x) :
    (nerveTwoCellBoundaryFunctor C a).map (Path.Homotopic.Quotient.mk p) =
      𝟙 ((nerveTwoCellBoundaryFunctor C a).obj (FundamentalGroupoid.mk x)) :=
  nerveTwoCell_boundary_loop_of_triangle C a (nerveTwoCell_triangle C a) x p

/-- Actual annulus naturality is inherited along the unchanged radial projection. -/
def nerveTwoCellAnnulusConstantIso (C : Type u) [Category.{v} C]
    (a : NerveTwoCellIndex C) :
    FundamentalGroupoid.map (annulusBoundary 2) ⋙ nerveTwoCellBoundaryFunctor C a ≅
      (Functor.const (FundamentalGroupoid (simplexAnnulus 2))).obj
        ((nerveTwoCellBoundaryFunctor C a).obj (FundamentalGroupoid.mk (vertex 0))) :=
  annulusConstantIsoOfTriangle _ (nerveTwoCell_triangle C a)

/-- Every actual radially projected two-cell annulus loop is killed, without
assuming that the annulus itself is simply connected. -/
theorem nerveTwoCell_annulus_loop (C : Type u) [Category.{v} C]
    (a : NerveTwoCellIndex C) (x : simplexAnnulus 2) (p : Path x x) :
    (FundamentalGroupoid.map (annulusBoundary 2) ⋙ nerveTwoCellBoundaryFunctor C a).map
        (Path.Homotopic.Quotient.mk p) =
      𝟙 ((nerveTwoCellBoundaryFunctor C a).obj
        (FundamentalGroupoid.mk (annulusBoundary 2 x))) :=
  nerveTwoCell_annulus_loop_of_triangle C a (nerveTwoCell_triangle C a) x p

end CategoryTheory.NerveCompletion
