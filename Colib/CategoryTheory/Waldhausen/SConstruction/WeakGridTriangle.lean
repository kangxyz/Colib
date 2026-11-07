/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.NerveTriangle
public import Colib.CategoryTheory.Waldhausen.SConstruction.WeakGridHomotopy

/-!
# Actual diagonal triangles from two composable weak-grid families

The two original component reindexing laws produce a genuine simplicial Δ[2] family. Its faces
are the original weak-grid cylinders, including the actual composite transformation cylinder.
-/
/- Implementation provenance: adapted from
   Quillen/Waldhausen/SConstruction/WeakGridTriangle.lean
   at c561118b7795eb9780be9ed391c3251d6a4d0afd. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite MonoidalCategory
open scoped Simplicial
universe v u

namespace CategoryTheory.Waldhausen

variable {D : Type u} [Category.{v} D] (W : Structure D)
  {X : SimplexCategoryᵒᵖ ⥤ SSet.{max u v}}
  (f g h : X ⟶ bisimplicialSSet W)
  (η : ∀ (n m : SimplexCategoryᵒᵖ) (x : (X.obj n).obj m),
    (((f.app n).app m) x).1 ⟶ (((g.app n).app m) x).1)
  (θ : ∀ (n m : SimplexCategoryᵒᵖ) (x : (X.obj n).obj m),
    (((g.app n).app m) x).1 ⟶ (((h.app n).app m) x).1)
  (hη : ∀ n m x p, W.weq ((η n m x).app p))
  (hθ : ∀ n m x p, W.weq ((θ n m x).app p))
  (hcompatη : ∀ {n n' : SimplexCategoryᵒᵖ} (α : n ⟶ n')
    (x : (SSet.diagonalSSet X).obj n) (p : Grid₂ n'.unop n'.unop),
    HEq ((η n' n' ((SSet.diagonalSSet X).map α x)).app p)
      ((η n n x).app ((gridMap₂ α.unop α.unop).obj p)))
  (hcompatθ : ∀ {n n' : SimplexCategoryᵒᵖ} (α : n ⟶ n')
    (x : (SSet.diagonalSSet X).obj n) (p : Grid₂ n'.unop n'.unop),
    HEq ((θ n' n' ((SSet.diagonalSSet X).map α x)).app p)
      ((θ n n x).app ((gridMap₂ α.unop α.unop).obj p)))

/-- The actual Δ[2] simplicial family obtained from the two composable weak families. -/
def weakGridFamilyTriangle :
    SSet.diagonalSSet X ⊗ Δ[2] ⟶ SSet.diagonalSSet (bisimplicialSSet W) where
  app n := ↾fun z ↦ ⟨nerveTriangleDiagram (η n n z.1) (θ n n z.1) z.2.down,
    nerveTriangleDiagram_isSimplex₂ W (η n n z.1) (θ n n z.1)
      (hη n n z.1) (hθ n n z.1) ((((f.app n).app n) z.1).2)
      ((((g.app n).app n) z.1).2) ((((h.app n).app n) z.1).2) z.2.down⟩
  naturality n n' α := by
    ext z
    apply Subtype.ext
    change nerveTriangleDiagram (η n' n' ((SSet.diagonalSSet X).map α z.1))
        (θ n' n' ((SSet.diagonalSSet X).map α z.1)) (α.unop ≫ z.2.down) =
      gridMap₂ α.unop α.unop ⋙ nerveTriangleDiagram (η n n z.1) (θ n n z.1) z.2.down
    exact (nerveTriangleDiagram_congr_app _ _ _ _ (diagonalGridMap_reindex W f α z.1)
      (diagonalGridMap_reindex W g α z.1) (diagonalGridMap_reindex W h α z.1)
      (hcompatη α z.1) (hcompatθ α z.1) (α.unop ≫ z.2.down)).trans
      (nerveTriangleDiagram_precomp (η n n z.1) (θ n n z.1) α.unop α.unop z.2.down)

/-- The first face is the unchanged cylinder of the first supplied transformation. -/
theorem weakGridFamilyTriangle_first :
    ((𝟙 (SSet.diagonalSSet X)) ⊗ₘ SSet.stdSimplex.δ 2) ≫
        weakGridFamilyTriangle W f g h η θ hη hθ hcompatη hcompatθ =
      weakGridFamilyCylinder W f g η hη hcompatη := by
  ext n z
  apply Subtype.ext
  exact nerveTriangleDiagram_first (η n n z.1) (θ n n z.1) z.2.down

/-- The second face is the unchanged cylinder of the second supplied transformation. -/
theorem weakGridFamilyTriangle_second :
    ((𝟙 (SSet.diagonalSSet X)) ⊗ₘ SSet.stdSimplex.δ 0) ≫
        weakGridFamilyTriangle W f g h η θ hη hθ hcompatη hcompatθ =
      weakGridFamilyCylinder W g h θ hθ hcompatθ := by
  ext n z
  apply Subtype.ext
  exact nerveTriangleDiagram_second (η n n z.1) (θ n n z.1) z.2.down

include hcompatη hcompatθ in
/-- The actual composite components retain their reindexing law. -/
theorem weakGridFamily_comp_compat {n n' : SimplexCategoryᵒᵖ} (α : n ⟶ n')
    (x : (SSet.diagonalSSet X).obj n) (p : Grid₂ n'.unop n'.unop) :
    HEq (((η n' n' ((SSet.diagonalSSet X).map α x)) ≫
      (θ n' n' ((SSet.diagonalSSet X).map α x))).app p)
      (((η n n x) ≫ (θ n n x)).app ((gridMap₂ α.unop α.unop).obj p)) :=
  heq_comp (congrArg (fun A ↦ A.obj p) (diagonalGridMap_reindex W f α x))
    (congrArg (fun A ↦ A.obj p) (diagonalGridMap_reindex W g α x))
    (congrArg (fun A ↦ A.obj p) (diagonalGridMap_reindex W h α x))
    (hcompatη α x p) (hcompatθ α x p)

/-- The long face is the cylinder of the genuine composite transformation. -/
theorem weakGridFamilyTriangle_composite :
    ((𝟙 (SSet.diagonalSSet X)) ⊗ₘ SSet.stdSimplex.δ 1) ≫
        weakGridFamilyTriangle W f g h η θ hη hθ hcompatη hcompatθ =
      weakGridFamilyCylinder W f h (fun n m x ↦ η n m x ≫ θ n m x)
        (fun n m x p ↦ W.weq.comp_mem _ _ (hη n m x p) (hθ n m x p))
        (weakGridFamily_comp_compat W f g h η θ hcompatη hcompatθ) := by
  ext n z
  apply Subtype.ext
  exact nerveTriangleDiagram_composite (η n n z.1) (θ n n z.1) z.2.down

end CategoryTheory.Waldhausen
