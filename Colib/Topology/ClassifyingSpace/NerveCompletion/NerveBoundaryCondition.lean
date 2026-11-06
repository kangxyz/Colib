/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Realization.SimplexBoundary.AnnulusLoops
public import Colib.Topology.ClassifyingSpace.NerveCompletion.NerveGraphDecoder

/-!
# Nerve Boundary Condition

The original nondegenerate two-cell indices, with independent category universes.
-/

@[expose] public section

noncomputable section
open CategoryTheory Convexity.StdSimplex FundamentalGroupoid.OpenCover SSet TopCat
universe u v
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover TopCat.SimplexAttachment Convexity.StdSimplex.Boundary
attribute [local instance] Localization.groupoid

/-- The original nondegenerate two-cell indices, with independent category universes. -/
abbrev NerveTwoCellIndex (C : Type u) [Category.{v} C] :=
  skeletalCellIndex (NerveGraphData.emptyMap C) 2

/-- The actual original two-cell attaching map into the actual nerve graph stage. -/
def nerveTwoCellBoundaryMap (C : Type u) [Category.{v} C] (a : NerveTwoCellIndex C) :
    C(simplexBoundary 2, NerveGraphData.Stage C) where
  toFun x := realizedSkeletalAttaching (NerveGraphData.emptyMap C) 2 (a, x)
  continuous_toFun := (realizedSkeletalAttaching (NerveGraphData.emptyMap C) 2).hom.continuous.comp
    (continuous_const.prodMk continuous_id)

/-- Pull back the already constructed actual graph decoder along that unchanged
attaching map. This definition does not assume any boundary loop equation. -/
def nerveTwoCellBoundaryFunctor (C : Type u) [Category.{v} C] (a : NerveTwoCellIndex C) :
    FundamentalGroupoid (simplexBoundary 2) ⥤ (⊤ : MorphismProperty C).Localization :=
  FundamentalGroupoid.map (nerveTwoCellBoundaryMap C a) ⋙ nerveGraphDecoder C

/-- The remaining nerve-specific hypothesis is explicitly the triangle relation
for these three ACTUAL attached boundary edges. Under it, every original
boundary loop is killed. The nerve-specific proof is in `NerveTriangle`. -/
theorem nerveTwoCell_boundary_loop_of_triangle (C : Type u) [Category.{v} C]
    (a : NerveTwoCellIndex C)
    (h : edgeMap (nerveTwoCellBoundaryFunctor C a) 0 1 ≫
        edgeMap (nerveTwoCellBoundaryFunctor C a) 1 2 =
      edgeMap (nerveTwoCellBoundaryFunctor C a) 0 2)
    (x : simplexBoundary 2) (p : Path x x) :
    (nerveTwoCellBoundaryFunctor C a).map (Path.Homotopic.Quotient.mk p) =
      𝟙 ((nerveTwoCellBoundaryFunctor C a).obj (FundamentalGroupoid.mk x)) :=
  boundary_loop_eq_id_of_triangle _ h x p

/-- The same explicit nerve-specific triangle hypothesis kills every actual
radially projected annulus loop, exactly the loop condition needed for the
collar overlap construction. No full-realization faithfulness is inferred. -/
theorem nerveTwoCell_annulus_loop_of_triangle (C : Type u) [Category.{v} C]
    (a : NerveTwoCellIndex C)
    (h : edgeMap (nerveTwoCellBoundaryFunctor C a) 0 1 ≫
        edgeMap (nerveTwoCellBoundaryFunctor C a) 1 2 =
      edgeMap (nerveTwoCellBoundaryFunctor C a) 0 2)
    (x : simplexAnnulus 2) (p : Path x x) :
    (FundamentalGroupoid.map (annulusBoundary 2) ⋙ nerveTwoCellBoundaryFunctor C a).map
        (Path.Homotopic.Quotient.mk p) =
      𝟙 ((nerveTwoCellBoundaryFunctor C a).obj
        (FundamentalGroupoid.mk (annulusBoundary 2 x))) :=
  annulus_loop_eq_id_of_triangle _ h x p

end CategoryTheory.NerveCompletion
