/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# The diagonal of a bisimplicial set

The diagonal is restriction along Mathlib's `Functor.diag` after uncurrying.
The two directions remain genuine simplicial directions. This is unrelated
to the long-edge map named `SimplicialObject.diagonal`.

Implementation provenance: extracted from `Quillen/CategoryTheory/TheoremA/Diagonal.lean`,
lines 34–63, at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
No simplicial replacement or Theorem A hypotheses are imported.
Isolated strict compilation is recorded in the accompanying release report.
-/
@[expose] public section


noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SSet

/-- The diagonal of a bisimplicial set. -/
def diagonalSSet (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) : SSet.{u} :=
  Functor.diag SimplexCategoryᵒᵖ ⋙ Functor.uncurry.obj X

/-- A map of bisimplicial sets gives a map on diagonals. -/
def diagonalMap {X Y : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (η : X ⟶ Y) :
    diagonalSSet X ⟶ diagonalSSet Y :=
  Functor.whiskerLeft (Functor.diag SimplexCategoryᵒᵖ) (Functor.uncurry.map η)

/-- Taking diagonals is functorial on bisimplicial sets. -/
def diagonalFunctor : (SimplexCategoryᵒᵖ ⥤ SSet.{u}) ⥤ SSet.{u} where
  obj X := diagonalSSet X
  map η := diagonalMap η

/-- Interchanging the two simplicial directions does not change the diagonal. -/
def diagonalFlipIso (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    diagonalSSet X.flip ≅ diagonalSSet X :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro p q α
    simp [diagonalSSet])

/-- The diagonal transpose isomorphism is natural in the bisimplicial set. -/
theorem diagonalFlipIso_naturality {X Y : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (η : X ⟶ Y) :
    diagonalMap ((CategoryTheory.flipFunctor _ _ _).map η) ≫ (diagonalFlipIso Y).hom =
      (diagonalFlipIso X).hom ≫ diagonalMap η := by
  ext p x : 4
  rfl


end SSet
