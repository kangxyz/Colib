/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.WeakNaturalTransformation

public import Colib.CategoryTheory.Waldhausen.SConstruction.WeakGridHomotopy
public import Colib.CategoryTheory.Waldhausen.SConstruction.NerveCylinderZero

/-! # Fixed-vertex weak-grid homotopies from actual zero diagrams

Implementation provenance: `Quillen/Waldhausen/SConstruction/WeakGridBasedHomotopy.lean`
at commit c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps, hypotheses and
universes are retained; no subdivision realization equivalence is assumed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped Simplicial
universe v u

namespace CategoryTheory.Waldhausen

variable {D : Type u} [Category.{v} D]

/-- The actual chosen-zero vertex of the diagonal bisimplicial model. -/
def diagonalZeroVertex (W : Structure D) :
    (SSet.diagonalSSet (bisimplicialSSet W)).obj (op ⦋0⦌) :=
  zeroSimplex₂ W.cof W.weq W.zero W.isZero (op ⦋0⦌) (op ⦋0⦌)

variable (W : Structure D)
  {X : SimplexCategoryᵒᵖ ⥤ SSet.{max u v}}
  (f g : X ⟶ bisimplicialSSet W)
  (η : ∀ (n m : SimplexCategoryᵒᵖ) (x : (X.obj n).obj m),
    (((f.app n).app m) x).1 ⟶ (((g.app n).app m) x).1)
  (hη : ∀ n m x p, W.weq ((η n m x).app p))
  (hcompat : ∀ {n n' : SimplexCategoryᵒᵖ} (α : n ⟶ n')
    (x : (SSet.diagonalSSet X).obj n) (p : Grid₂ n'.unop n'.unop),
    HEq ((η n' n' ((SSet.diagonalSSet X).map α x)).app p)
      ((η n n x).app ((gridMap₂ α.unop α.unop).obj p)))
  (x : (SSet.diagonalSSet X) _⦋0⦌)
  (hf : ∀ (n : SimplexCategoryᵒᵖ) (z : (Δ[0] : SSet.{max u v}).obj n) p,
    ((((f.app n).app n) ((SSet.yonedaEquiv.symm x).app n z)).1.obj p) = W.zero)
  (hg : ∀ (n : SimplexCategoryᵒᵖ) (z : (Δ[0] : SSet.{max u v}).obj n) p,
    ((((g.app n).app n) ((SSet.yonedaEquiv.symm x).app n z)).1.obj p) = W.zero)

include hf hg

/-- Actual zero values of both endpoint grids force the entire vertex track
to be literally the constant chosen-zero simplex. -/
theorem weakGridFamilyCylinder_fixed_vertex :
    SSet.yonedaEquiv.symm x ▷ Δ[1] ≫ weakGridFamilyCylinder W f g η hη hcompat =
      CartesianMonoidalCategory.fst Δ[0] Δ[1] ≫
        SSet.yonedaEquiv.symm (diagonalZeroVertex W) := by
  ext n z
  apply Subtype.ext
  exact nerveCylinderDiagram_eq_const_of_zero
    (η n n ((SSet.yonedaEquiv.symm x).app n z.1)) W.zero W.isZero
    (hf n z.1) (hg n z.1) z.2.down

/-- The actual realized homotopy is fixed at the specified source vertex,
proved from endpoint zero diagrams rather than an assumed fixed-track condition. -/
theorem diagonalWeakGridRealizationHomotopy_fixed_vertex (t : unitInterval) :
    diagonalWeakGridRealizationHomotopy W f g η hη hcompat (t, SSet.realizationPoint x) =
      SSet.realizationPoint (diagonalZeroVertex W) :=
  SSet.realizationSimplicialHomotopy_fixed_vertex
    (diagonalWeakGridHomotopy W f g η hη hcompat) x _
    (weakGridFamilyCylinder_fixed_vertex W f g η hη hcompat x hf hg) t

end CategoryTheory.Waldhausen
