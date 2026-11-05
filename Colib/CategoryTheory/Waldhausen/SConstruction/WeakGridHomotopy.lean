/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.SConstruction.NerveCylinderNaturality
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-! # Actual diagonal homotopies from weak natural-transformation families

The family compatibility condition concerns its actual transformation
components after grid reindexing. It does not assume naturality of the
resulting cylinder or a desired homotopy.
-/
/- Implementation provenance: adapted from
   Quillen/Waldhausen/SConstruction/WeakGridHomotopy.lean
   at c561118b7795eb9780be9ed391c3251d6a4d0afd.
   Validation status is recorded in the accompanying release report. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped Simplicial
universe v u

namespace CategoryTheory.Waldhausen

variable {D : Type u} [Category.{v} D] (W : Structure D)
  {X : SimplexCategoryᵒᵖ ⥤ SSet.{max u v}}
  (f g : X ⟶ bisimplicialSSet W)

/-- Bisimplicial-map naturality identifies the actual endpoint grid after
simultaneous reindexing, with no new compatibility assumption. -/
theorem diagonalGridMap_reindex {n n' : SimplexCategoryᵒᵖ} (α : n ⟶ n')
    (x : (SSet.diagonalSSet X).obj n) :
    (((f.app n').app n') ((SSet.diagonalSSet X).map α x)).1 =
      gridMap₂ α.unop α.unop ⋙ (((f.app n).app n) x).1 := by
  exact congrArg Subtype.val (ConcreteCategory.congr_hom
    ((SSet.diagonalMap f).naturality α) x)

variable
  (η : ∀ (n m : SimplexCategoryᵒᵖ) (x : (X.obj n).obj m),
    (((f.app n).app m) x).1 ⟶ (((g.app n).app m) x).1)
  (hη : ∀ n m x p, W.weq ((η n m x).app p))
  (hcompat : ∀ {n n' : SimplexCategoryᵒᵖ} (α : n ⟶ n')
    (x : (SSet.diagonalSSet X).obj n) (p : Grid₂ n'.unop n'.unop),
    HEq ((η n' n' ((SSet.diagonalSSet X).map α x)).app p)
      ((η n n x).app ((gridMap₂ α.unop α.unop).obj p)))

/-- The actual simplicial cylinder obtained by applying the categorical
nerve cylinder to each member of a compatible weak family. -/
def weakGridFamilyCylinder :
    SSet.diagonalSSet X ⊗ Δ[1] ⟶ SSet.diagonalSSet (bisimplicialSSet W) where
  app n := ↾fun z ↦ ⟨nerveCylinderDiagram (η n n z.1) z.2.down,
    nerveCylinderDiagram_isSimplex₂ W (η n n z.1) (hη n n z.1)
      ((((f.app n).app n) z.1).2) ((((g.app n).app n) z.1).2) z.2.down⟩
  naturality n n' α := by
    ext z
    apply Subtype.ext
    change nerveCylinderDiagram (η n' n' ((SSet.diagonalSSet X).map α z.1))
        (α.unop ≫ z.2.down) =
      gridMap₂ α.unop α.unop ⋙ nerveCylinderDiagram (η n n z.1) z.2.down
    exact (nerveCylinderDiagram_congr_app _ _ (diagonalGridMap_reindex W f α z.1)
      (diagonalGridMap_reindex W g α z.1) (hcompat α z.1) (α.unop ≫ z.2.down)).trans
      (nerveCylinderDiagram_precomp (η n n z.1) α.unop α.unop z.2.down)

/-- The zero endpoint is the original first diagonal map. -/
@[simp] theorem weakGridFamilyCylinder_zero :
    SSet.ι₀ ≫ weakGridFamilyCylinder W f g η hη hcompat = SSet.diagonalMap f := by
  ext n x
  apply Subtype.ext
  exact nerveCylinderDiagram_zero (η n n x)

/-- The one endpoint is the original second diagonal map. -/
@[simp] theorem weakGridFamilyCylinder_one :
    SSet.ι₁ ≫ weakGridFamilyCylinder W f g η hη hcompat = SSet.diagonalMap g := by
  ext n x
  apply Subtype.ext
  exact nerveCylinderDiagram_one (η n n x)

/-- A compatible family of actual pointwise weak natural transformations
gives a genuine simplicial homotopy with the original endpoint maps. -/
def diagonalWeakGridHomotopy :
    SSet.Homotopy (SSet.diagonalMap f) (SSet.diagonalMap g) where
  h := weakGridFamilyCylinder W f g η hη hcompat
  h₀ := weakGridFamilyCylinder_zero W f g η hη hcompat
  h₁ := weakGridFamilyCylinder_one W f g η hη hcompat
  rel := by ext n z; exact z.1.property.elim

end CategoryTheory.Waldhausen
