/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.GrothendieckComparison.GridTriangles
public import Colib.CategoryTheory.Waldhausen.Rows.OneRowIso

/-! # Every original diagonal edge reduces to its original object loop

The actual one-row reconstruction isomorphism and the two genuine grid
triangles identify each arbitrary original edge after closing it by coherent
original zero-object tracks. No assertion about generation of arbitrary
continuous paths is used here.

Implementation provenance: `Quillen/Waldhausen/GrothendieckComparison/EdgeNormalization.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
objects, maps and hypotheses are retained.
-/
@[expose] public section

open CategoryTheory.Waldhausen.QuotientRows


noncomputable section
open Topology SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u v
namespace CategoryTheory.Waldhausen.Structure
open QuotientRows
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- An original diagonal zero object of an original quotient row. -/
def rowZero (R : Obj W ⦋1⦌) (i : Fin 2) : ZeroObjects (C := C) :=
  ⟨R.obj.obj (interval i i le_rfl), R.property.zero i⟩

/-- The actual path class of the unchanged original diagonal edge. -/
def gridPathHom (X : (sSet W.cof W.weq) _⦋1⦌) :
    FundamentalGroupoid.mk
      (basepoint W.cof W.weq (W.gridZero X 0 0).obj (W.gridZero X 0 0).property) ⟶
    FundamentalGroupoid.mk
      (basepoint W.cof W.weq (W.gridZero X 1 1).obj (W.gridZero X 1 1).property) :=
  ⟦realizationEdgePath (W.gridEdge X)⟧

/-- The actual original row path, with its original zero endpoints. -/
def rowPathHom (R : Obj W ⦋1⦌) :
    FundamentalGroupoid.mk
      (basepoint W.cof W.weq (W.rowZero R 0).obj (W.rowZero R 0).property) ⟶
    FundamentalGroupoid.mk
      (basepoint W.cof W.weq (W.rowZero R 1).obj (W.rowZero R 1).property) :=
  W.gridPathHom (W.rowSimplex R)

/-- The actual upper triangle factors the original diagonal path. -/
theorem gridPathHom_upper (X : (sSet W.cof W.weq) _⦋1⦌) :
    W.rowPathHom (W.gridRow X 0) ≫
      W.zeroTrackHom (W.gridZero X 0 1) (W.gridZero X 1 1) = W.gridPathHom X :=
  Quotient.sound (realizationEdgePath_comp (W.gridUpperCompStruct X))

/-- The actual lower triangle factors the same original diagonal path. -/
theorem gridPathHom_lower (X : (sSet W.cof W.weq) _⦋1⦌) :
    W.zeroTrackHom (W.gridZero X 0 0) (W.gridZero X 1 0) ≫
      W.rowPathHom (W.gridRow X 1) = W.gridPathHom X :=
  Quotient.sound (realizationEdgePath_comp (W.gridLowerCompStruct X))

/-- The original one-row reconstruction isomorphism is an actual pointwise weak arrow. -/
def rowNormalizationArrow (R : Obj W ⦋1⦌) :
    (⟨(oneEmbedding W).obj ((oneEvaluation W).obj R)⟩ : WeakRows W ⦋1⦌) ⟶ ⟨R⟩ :=
  ⟨(oneRowIso W R).hom, QuotientRows.weq_iso W ⦋1⦌ _ inferInstance⟩

/-- Its original diagonal square retains the original arbitrary row. -/
def rowNormalizationSquare (R : Obj W ⦋1⦌) : (sSet W.cof W.weq) _⦋1⦌ :=
  ⟨weakChainToGrid W (ComposableArrows.mk₁ (W.rowNormalizationArrow R)),
    (isSimplex₂_diagonal_iff W.cof W.weq _).mp (weakChainToGrid_isSimplex₂ W _)⟩

/-- The first short edge is literally the original canonical object simplex. -/
theorem rowNormalizationSquare_source (R : Obj W ⦋1⦌) :
    W.rowSimplex (W.gridRow (W.rowNormalizationSquare R) 0) =
      W.kZeroObjectSimplex ((oneEvaluation W).obj R) := by
  apply Subtype.ext
  change intervalProjection ⦋1⦌ ⋙
    (gridRestriction 0 ⋙ weakChainToGrid W _) = _
  rw [weakChainToGrid_row]
  rfl

/-- The second short edge is literally the unchanged original arbitrary row simplex. -/
theorem rowNormalizationSquare_target (R : Obj W ⦋1⦌) :
    W.rowSimplex (W.gridRow (W.rowNormalizationSquare R) 1) = W.rowSimplex R := by
  apply Subtype.ext
  change intervalProjection ⦋1⦌ ⋙
    (gridRestriction 1 ⋙ weakChainToGrid W _) = _
  rw [weakChainToGrid_row]
  rfl

/-- The original upper normalization triangle uses the original object loop. -/
def rowNormalizationUpper (R : Obj W ⦋1⦌) :
    SSet.Edge.CompStruct (W.kZeroObjectEdge ((oneEvaluation W).obj R))
      (W.zeroTrackEdge W.chosenZeroObject (W.rowZero R 1))
      (W.gridEdge (W.rowNormalizationSquare R)) where
  simplex := W.gridTriangle (W.rowNormalizationSquare R) 1 0
  d₂ := (W.gridTriangle_source _).trans (W.rowNormalizationSquare_source R)
  d₀ := W.gridTriangle_upper_zero _
  d₁ := W.gridTriangle_middle _ 1 0

/-- The original lower normalization triangle uses the original arbitrary row path. -/
def rowNormalizationLower (R : Obj W ⦋1⦌) :
    SSet.Edge.CompStruct (W.zeroTrackEdge W.chosenZeroObject (W.rowZero R 0))
      (W.gridEdge (W.rowSimplex R)) (W.gridEdge (W.rowNormalizationSquare R)) where
  simplex := W.gridTriangle (W.rowNormalizationSquare R) 0 1
  d₂ := W.gridTriangle_lower_zero _
  d₀ := (W.gridTriangle_target _).trans (W.rowNormalizationSquare_target R)
  d₁ := W.gridTriangle_middle _ 0 1

/-- Closing an arbitrary original row with its coherent zero tracks gives its
original middle-object loop, as an equality of genuine path classes. -/
theorem rowPathHom_normalization (R : Obj W ⦋1⦌) :
    W.zeroAnchorHom (W.rowZero R 0) ≫ W.rowPathHom R =
      (⟦W.kZeroObjectLoop ((oneEvaluation W).obj R)⟧ :
        FundamentalGroupoid.mk W.kBasepoint ⟶ FundamentalGroupoid.mk W.kBasepoint) ≫
          W.zeroAnchorHom (W.rowZero R 1) := by
  exact (Quotient.sound (realizationEdgePath_comp (W.rowNormalizationLower R))).trans
    (Quotient.sound (realizationEdgePath_comp (W.rowNormalizationUpper R))).symm

/-- Every original diagonal edge, after its original chosen-zero anchoring,
is exactly the original object-loop class of its source-row middle object. -/
theorem gridPathHom_normalization (X : (sSet W.cof W.weq) _⦋1⦌) :
    W.zeroAnchorHom (W.gridZero X 0 0) ≫ W.gridPathHom X =
      (⟦W.kZeroObjectLoop (X.val.obj (grid 0 0 1 (by decide)))⟧ :
        FundamentalGroupoid.mk W.kBasepoint ⟶ FundamentalGroupoid.mk W.kBasepoint) ≫
          W.zeroAnchorHom (W.gridZero X 1 1) := by
  have hr := W.rowPathHom_normalization (W.gridRow X 0)
  change W.zeroAnchorHom (W.gridZero X 0 0) ≫ W.rowPathHom (W.gridRow X 0) =
    (⟦W.kZeroObjectLoop (X.val.obj (grid 0 0 1 (by decide)))⟧ :
      FundamentalGroupoid.mk W.kBasepoint ⟶ FundamentalGroupoid.mk W.kBasepoint) ≫
        W.zeroAnchorHom (W.gridZero X 0 1) at hr
  rw [← W.gridPathHom_upper X, ← Category.assoc, hr, Category.assoc, W.zeroAnchorHom_comp]

/-- The original anchored edge is literally its original object loop in the
actual based fundamental group, without a path-generation assumption. -/
theorem gridPathHom_normalization_closed (X : (sSet W.cof W.weq) _⦋1⦌) :
    W.zeroAnchorHom (W.gridZero X 0 0) ≫ W.gridPathHom X ≫
      inv (W.zeroAnchorHom (W.gridZero X 1 1)) =
        (⟦W.kZeroObjectLoop (X.val.obj (grid 0 0 1 (by decide)))⟧ :
          FundamentalGroupoid.mk W.kBasepoint ⟶ FundamentalGroupoid.mk W.kBasepoint) := by
  rw [← Category.assoc, W.gridPathHom_normalization]
  simp

end CategoryTheory.Waldhausen.Structure
