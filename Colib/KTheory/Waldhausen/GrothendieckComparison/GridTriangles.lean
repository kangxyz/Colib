/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.GrothendieckComparison.ZeroTracks
public import Colib.CategoryTheory.Waldhausen.Rows.NerveBridge

/-! # The two original triangles of every diagonal weak quotient-row square

Independent degeneracies split an arbitrary original one-simplex into its
original source or target row and the actual zero-object track on the opposite
boundary. The resulting relations hold in the genuine fundamental groupoid.

Implementation provenance: `Quillen/Waldhausen/GrothendieckComparison/GridTriangles.lean`
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

/-- An actual original diagonal zero object of the original grid. -/
def gridZero (X : (sSet W.cof W.weq) _⦋1⦌) (t i : Fin 2) : ZeroObjects (C := C) :=
  ⟨X.val.obj (grid t i i le_rfl), X.property.zero t i⟩

/-- An actual original row of the original weak quotient-grid square. -/
def gridRow (X : (sSet W.cof W.weq) _⦋1⦌) (t : Fin 2) : Obj W ⦋1⦌ :=
  ⟨gridRestriction t ⋙ X.val,
    isRow_of_isSimplex₂ W ((isSimplex₂_diagonal_iff W.cof W.weq _).mpr X.property) t⟩

/-- The original one-simplex as an edge between its actual original zero vertices. -/
def gridEdge (X : (sSet W.cof W.weq) _⦋1⦌) :
    (sSet W.cof W.weq).Edge
      (zeroSimplex W.cof W.weq (W.gridZero X 0 0).obj (W.gridZero X 0 0).property (op ⦋0⦌))
      (zeroSimplex W.cof W.weq (W.gridZero X 1 1).obj (W.gridZero X 1 1).property (op ⦋0⦌)) where
  edge := X
  src_eq := by
    apply Subtype.ext
    have hobj : ∀ p, ((sSet W.cof W.weq).δ 1 X).val.obj p = (W.gridZero X 0 0).obj := by
      rintro ⟨t, ⟨⟨a,b⟩, hab⟩⟩
      fin_cases t; fin_cases a; fin_cases b; rfl
    refine CategoryTheory.Functor.ext hobj ?_
    intro p q f
    have hz : IsZero (((sSet W.cof W.weq).δ 1 X).val.obj p) := by
      rw [hobj p]
      exact (W.gridZero X 0 0).property
    exact hz.eq_of_src _ _
  tgt_eq := by
    apply Subtype.ext
    have hobj : ∀ p, ((sSet W.cof W.weq).δ 0 X).val.obj p = (W.gridZero X 1 1).obj := by
      rintro ⟨t, ⟨⟨a,b⟩, hab⟩⟩
      fin_cases t; fin_cases a; fin_cases b; rfl
    refine CategoryTheory.Functor.ext hobj ?_
    intro p q f
    have hz : IsZero (((sSet W.cof W.weq).δ 0 X).val.obj p) := by
      rw [hobj p]
      exact (W.gridZero X 1 1).property
    exact hz.eq_of_src _ _

/-- Independently degenerate any original square in its interval and nerve directions. -/
def gridTriangle (X : (sSet W.cof W.weq) _⦋1⦌) (i j : Fin 2) :
    (sSet W.cof W.weq) _⦋2⦌ :=
  ⟨gridMap₂ (SimplexCategory.σ i) (SimplexCategory.σ j) ⋙ X.val,
    (isSimplex₂_diagonal_iff W.cof W.weq _).mp
      (((isSimplex₂_diagonal_iff W.cof W.weq _).mpr X.property).precomp W.cof W.weq _ _)⟩

/-- The diagonal edge of either triangle is the unchanged original square. -/
theorem gridTriangle_middle (X : (sSet W.cof W.weq) _⦋1⦌) (i j : Fin 2) :
    (sSet W.cof W.weq).δ 1 (W.gridTriangle X i j) = X := by
  apply Subtype.ext
  change gridMap (SimplexCategory.δ 1) ⋙
    (gridMap₂ (SimplexCategory.σ i) (SimplexCategory.σ j) ⋙ _) = _
  have hidx : gridMap (SimplexCategory.δ 1) ⋙
      gridMap₂ (SimplexCategory.σ i) (SimplexCategory.σ j) = 𝟭 (Grid ⦋1⦌) := by
    apply CategoryTheory.Functor.ext (fun p ↦ ?_)
    rcases p with ⟨t, ⟨⟨a,b⟩, hab⟩⟩
    fin_cases i <;> fin_cases j <;> fin_cases t <;> fin_cases a <;> fin_cases b <;> rfl
  rw [← Functor.assoc, hidx, Functor.id_comp]

/-- The upper triangle retains the complete original source row. -/
theorem gridTriangle_source (X : (sSet W.cof W.weq) _⦋1⦌) :
    (sSet W.cof W.weq).δ 2 (W.gridTriangle X 1 0) = W.rowSimplex (W.gridRow X 0) := by
  apply Subtype.ext
  change gridMap (SimplexCategory.δ 2) ⋙
    (gridMap₂ (SimplexCategory.σ 1) (SimplexCategory.σ 0) ⋙ _) = _
  have hidx : gridMap (SimplexCategory.δ 2) ⋙
      gridMap₂ (SimplexCategory.σ 1) (SimplexCategory.σ 0) =
        intervalProjection ⦋1⦌ ⋙ gridRestriction (n := ⦋1⦌) (m := ⦋1⦌) 0 := by
    apply CategoryTheory.Functor.ext (fun p ↦ ?_)
    rcases p with ⟨t, ⟨⟨a,b⟩, hab⟩⟩
    fin_cases t <;> fin_cases a <;> fin_cases b <;> rfl
  rw [← Functor.assoc, hidx, Functor.assoc]
  rfl

/-- The lower triangle retains the complete original target row. -/
theorem gridTriangle_target (X : (sSet W.cof W.weq) _⦋1⦌) :
    (sSet W.cof W.weq).δ 0 (W.gridTriangle X 0 1) = W.rowSimplex (W.gridRow X 1) := by
  apply Subtype.ext
  change gridMap (SimplexCategory.δ 0) ⋙
    (gridMap₂ (SimplexCategory.σ 0) (SimplexCategory.σ 1) ⋙ _) = _
  have hidx : gridMap (SimplexCategory.δ 0) ⋙
      gridMap₂ (SimplexCategory.σ 0) (SimplexCategory.σ 1) =
        intervalProjection ⦋1⦌ ⋙ gridRestriction (n := ⦋1⦌) (m := ⦋1⦌) 1 := by
    apply CategoryTheory.Functor.ext (fun p ↦ ?_)
    rcases p with ⟨t, ⟨⟨a,b⟩, hab⟩⟩
    fin_cases t <;> fin_cases a <;> fin_cases b <;> rfl
  rw [← Functor.assoc, hidx, Functor.assoc]
  rfl

/-- The other upper edge is precisely the original target-diagonal zero track. -/
theorem gridTriangle_upper_zero (X : (sSet W.cof W.weq) _⦋1⦌) :
    (sSet W.cof W.weq).δ 0 (W.gridTriangle X 1 0) =
      (W.zeroTrackEdge (W.gridZero X 0 1) (W.gridZero X 1 1)).edge := by
  apply Subtype.ext
  have hobj : ∀ p, ((sSet W.cof W.weq).δ 0 (W.gridTriangle X 1 0)).val.obj p =
      (W.zeroTrackEdge (W.gridZero X 0 1) (W.gridZero X 1 1)).edge.val.obj p := by
    rintro ⟨t, ⟨⟨a,b⟩, hab⟩⟩
    fin_cases t <;> fin_cases a <;> fin_cases b <;> rfl
  refine CategoryTheory.Functor.ext hobj ?_
  intro p q f
  have hz : IsZero (((sSet W.cof W.weq).δ 0 (W.gridTriangle X 1 0)).val.obj p) := by
    rcases p with ⟨t, ⟨⟨a,b⟩, hab⟩⟩
    fin_cases t <;> fin_cases a <;> fin_cases b <;> exact X.property.zero _ _
  exact hz.eq_of_src _ _

/-- The other lower edge is precisely the original source-diagonal zero track. -/
theorem gridTriangle_lower_zero (X : (sSet W.cof W.weq) _⦋1⦌) :
    (sSet W.cof W.weq).δ 2 (W.gridTriangle X 0 1) =
      (W.zeroTrackEdge (W.gridZero X 0 0) (W.gridZero X 1 0)).edge := by
  apply Subtype.ext
  have hobj : ∀ p, ((sSet W.cof W.weq).δ 2 (W.gridTriangle X 0 1)).val.obj p =
      (W.zeroTrackEdge (W.gridZero X 0 0) (W.gridZero X 1 0)).edge.val.obj p := by
    rintro ⟨t, ⟨⟨a,b⟩, hab⟩⟩
    fin_cases t <;> fin_cases a <;> fin_cases b <;> rfl
  refine CategoryTheory.Functor.ext hobj ?_
  intro p q f
  have hz : IsZero (((sSet W.cof W.weq).δ 2 (W.gridTriangle X 0 1)).val.obj p) := by
    rcases p with ⟨t, ⟨⟨a,b⟩, hab⟩⟩
    fin_cases t <;> fin_cases a <;> fin_cases b <;> exact X.property.zero _ _
  exact hz.eq_of_src _ _

/-- The original upper triangle supplies an actual edge composition structure. -/
def gridUpperCompStruct (X : (sSet W.cof W.weq) _⦋1⦌) :
    SSet.Edge.CompStruct (W.gridEdge (W.rowSimplex (W.gridRow X 0)))
      (W.zeroTrackEdge (W.gridZero X 0 1) (W.gridZero X 1 1)) (W.gridEdge X) where
  simplex := W.gridTriangle X 1 0
  d₂ := W.gridTriangle_source X
  d₀ := W.gridTriangle_upper_zero X
  d₁ := W.gridTriangle_middle X 1 0

/-- The original lower triangle supplies an actual edge composition structure. -/
def gridLowerCompStruct (X : (sSet W.cof W.weq) _⦋1⦌) :
    SSet.Edge.CompStruct (W.zeroTrackEdge (W.gridZero X 0 0) (W.gridZero X 1 0))
      (W.gridEdge (W.rowSimplex (W.gridRow X 1))) (W.gridEdge X) where
  simplex := W.gridTriangle X 0 1
  d₂ := W.gridTriangle_lower_zero X
  d₀ := W.gridTriangle_target X
  d₁ := W.gridTriangle_middle X 0 1

end CategoryTheory.Waldhausen.Structure
