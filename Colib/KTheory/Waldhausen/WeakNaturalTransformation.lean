/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.WeakNaturalTransformation
public import Colib.KTheory.Waldhausen.Map
public import Colib.Topology.Realization.HomotopyBridge

/-! # Realization of actual weak natural transformations

Adapted from WeakGridHomotopy and WeakNaturalTransformation at Quillen commit
c561118b7795eb9780be9ed391c3251d6a4d0afd. Realization is separated from the lower
simplicial cylinder. No basedness is asserted without an actual fixed-zero proof.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped Simplicial
universe v u
namespace CategoryTheory.Waldhausen
section GridFamily
variable {D : Type u} [Category.{v} D] (W : Structure D)
  {X : SimplexCategoryᵒᵖ ⥤ SSet.{max u v}}
  (f g : X ⟶ bisimplicialSSet W)

variable
  (η : ∀ (n m : SimplexCategoryᵒᵖ) (x : (X.obj n).obj m),
    (((f.app n).app m) x).1 ⟶ (((g.app n).app m) x).1)
  (hη : ∀ n m x p, W.weq ((η n m x).app p))
  (hcompat : ∀ {n n' : SimplexCategoryᵒᵖ} (α : n ⟶ n')
    (x : (SSet.diagonalSSet X).obj n) (p : Grid₂ n'.unop n'.unop),
    HEq ((η n' n' ((SSet.diagonalSSet X).map α x)).app p)
      ((η n n x).app ((gridMap₂ α.unop α.unop).obj p)))


/-- Realization preserves the exact original endpoint maps of this homotopy.
No basedness is asserted without a separate zero-component condition. -/
def diagonalWeakGridRealizationHomotopy :
    (SSet.toTop.map (SSet.diagonalMap f)).hom.Homotopy
      (SSet.toTop.map (SSet.diagonalMap g)).hom :=
  SSet.realizationSimplicialHomotopy (diagonalWeakGridHomotopy W f g η hη hcompat)

end GridFamily

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) {F G : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact V.cof V.weq W.cof W.weq G)
  (η : F ⟶ G) (hη : ∀ X, W.weq (η.app X))


/-- The homotopy of actual realization maps, with the exact original endpoints. -/
def weakNaturalTransformationRealizationHomotopy :
    (deloopingMap hF).hom.Homotopy (deloopingMap hG).hom :=
  SSet.realizationSimplicialHomotopy (weakNaturalTransformationHomotopy V W hF hG η hη)

end CategoryTheory.Waldhausen

attribute [colib_tag "COL-0156",
  colib_ref "Waldhausen1985" "Section 1.3, pp. 328-330" "background"
    "Background for the stated unnormalized IsZero model; not a strict-model identification"]
  CategoryTheory.Waldhausen.weakNaturalTransformationRealizationHomotopy
