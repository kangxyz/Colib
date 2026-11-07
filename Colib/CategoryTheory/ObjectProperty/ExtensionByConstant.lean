/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.EqToHom

/-!
Implementation provenance: `Quillen/Aglib/CategoryTheory/ObjectProperty/ExtensionByConstant.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Extending a functor constantly outside a union of components -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u v w w'
namespace CategoryTheory.ObjectProperty
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} {D : Type w} [Category.{v} C] [Category.{w'} D]
variable (P : CategoryTheory.ObjectProperty C) (F : P.FullSubcategory ⥤ D) (d : D)
variable (hstable : ∀ {X Y : C}, (X ⟶ Y) → (P X ↔ P Y))

/-- The original functor object on the selected components, and the chosen constant elsewhere. -/
def extensionObject (X : C) : D := by
  classical
  exact if h : P X then F.obj ⟨X, h⟩ else d

/-- The original morphism on the selected components and the constant identity elsewhere. -/
def extensionMap {X Y : C} (f : X ⟶ Y) : extensionObject P F d X ⟶ extensionObject P F d Y := by
  classical
  by_cases hx : P X
  · have hy := (hstable f).1 hx
    exact eqToHom (by simp [extensionObject, hx]) ≫
      F.map (CategoryTheory.ObjectProperty.homMk (X := ⟨X, hx⟩) (Y := ⟨Y, hy⟩) f) ≫
      eqToHom (by simp [extensionObject, hy])
  · have hy : ¬ P Y := fun hy => hx ((hstable f).2 hy)
    exact eqToHom (by simp [extensionObject, hx, hy])

theorem map_homMk_id (X : C) (hx : P X) :
    F.map (CategoryTheory.ObjectProperty.homMk (X := ⟨X, hx⟩) (𝟙 X)) =
      𝟙 (F.obj ⟨X, hx⟩) := F.map_id _

theorem map_homMk_comp {X Y Z : C} (hx : P X) (hy : P Y) (hz : P Z)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.map (CategoryTheory.ObjectProperty.homMk (X := ⟨X, hx⟩) (Y := ⟨Z, hz⟩) (f ≫ g)) =
      F.map (CategoryTheory.ObjectProperty.homMk (X := ⟨X, hx⟩) (Y := ⟨Y, hy⟩) f) ≫
      F.map (CategoryTheory.ObjectProperty.homMk (X := ⟨Y, hy⟩) (Y := ⟨Z, hz⟩) g) :=
  F.map_comp (CategoryTheory.ObjectProperty.homMk (X := ⟨X, hx⟩) (Y := ⟨Y, hy⟩) f)
    (CategoryTheory.ObjectProperty.homMk (X := ⟨Y, hy⟩) (Y := ⟨Z, hz⟩) g)

/-- Extend a functor by a constant on the other entire components. -/
def extensionByConstant : C ⥤ D where
  obj := extensionObject P F d
  map := extensionMap P F d hstable
  map_id X := by
    classical
    by_cases hx : P X
    · simp [extensionMap, hx, map_homMk_id]
    · simp [extensionMap, hx]
  map_comp {X Y Z} f g := by
    classical
    by_cases hx : P X
    · have hy := (hstable f).1 hx
      have hz := (hstable g).1 hy
      simp only [extensionMap, dite_eq_left hx, dite_eq_left hy]
      rw [map_homMk_comp P F hx hy hz]
      simp [Category.assoc]
    · have hy : ¬ P Y := fun hy => hx ((hstable f).2 hy)
      have hz : ¬ P Z := fun hz => hy ((hstable g).2 hz)
      simp [extensionMap, hx, hy]

/-- Restriction to the chosen full subcategory recovers the original functor. -/
def extensionByConstantIso : P.ι ⋙ extensionByConstant P F d hstable ≅ F :=
  NatIso.ofComponents
    (fun X => eqToIso (by simp [extensionByConstant, extensionObject, X.property])) (by
      intro X Y f
      dsimp [extensionByConstant]
      simp only [extensionMap, dite_eq_left X.property, Category.assoc,
        eqToHom_trans, eqToHom_refl, Category.comp_id]
      rfl)

end CategoryTheory.ObjectProperty
