/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.Structure
public import Colib.CategoryTheory.Waldhausen.Rows.Basic

/-! # Reedy cofibrations on the original quotient-row category

The all-triples relative-arrow condition is imposed on the existing full row
category, with its original pointwise weak maps and chosen zero.

Implementation provenance: `Quillen/Waldhausen/SConstruction/Rows/Basic.lean`
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`, cofibration declarations.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.QuotientRows
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- Restriction to a horizontal interval arrow is an actual cofibration-arrow functor. -/
def horizontalArrow {n : SimplexCategory} (i j k : Fin (n.len + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    Obj W n ⥤ ExtensionCategory.Obj W where
  obj F := ⟨Arrow.mk (F.obj.map (homOfLE
    (show interval i j hij ≤ interval i k (hij.trans hjk) from ⟨le_rfl, hjk⟩))),
    F.property.cofibration i j k hij hjk⟩
  map η := (ExtensionCategory.objects W).homMk
    (Arrow.homMk (η.hom.app _) (η.hom.app _) (η.hom.naturality _).symm)
  map_id _ := by apply ObjectProperty.hom_ext; apply Arrow.hom_ext <;> rfl
  map_comp _ _ := by apply ObjectProperty.hom_ext; apply Arrow.hom_ext <;> rfl

/-- Genuine Reedy cofibrations on every horizontal interval-arrow square. -/
def cof (n : SimplexCategory) : MorphismProperty (Obj W n) := fun _ _ η ↦
  ∀ i j k hij hjk, ExtensionCategory.cof W ((horizontalArrow W i j k hij hjk).map η)

/-- The degenerate horizontal arrows explicitly recover every component cofibration. -/
theorem cof_app {n : SimplexCategory} {F G : Obj W n} {η : F ⟶ G}
    (hη : cof W n η) (p : Interval n) : W.cof (η.hom.app p) :=
  (hη p.val.1 p.val.2 p.val.2 p.property le_rfl).1

instance cof_multiplicative (n : SimplexCategory) : (cof W n).IsMultiplicative where
  id_mem F := by
    intro i j k hij hjk
    simpa only [CategoryTheory.Functor.map_id] using
      (ExtensionCategory.cof W).id_mem ((horizontalArrow W i j k hij hjk).obj F)
  comp_mem η θ hη hθ := by
    intro i j k hij hjk
    simpa only [CategoryTheory.Functor.map_comp] using
      (ExtensionCategory.cof W).comp_mem _ _ (hη i j k hij hjk) (hθ i j k hij hjk)

theorem cof_iso (n : SimplexCategory) : MorphismProperty.isomorphisms (Obj W n) ≤ cof W n := by
  intro F G η hη i j k hij hjk
  let : IsIso η := hη
  exact ExtensionCategory.cof_iso W _ inferInstance

/-- The zero-to-row transformation satisfies every actual relative cofibration test. -/
theorem cof_zero (n : SimplexCategory) (F : Obj W n) : cof W n ((isZero W n).to_ F) := by
  intro i j k hij hjk
  have h : (horizontalArrow W i j k hij hjk).map ((isZero W n).to_ F) =
      ExtensionCategory.fromZero W ((horizontalArrow W i j k hij hjk).obj F) :=
    (ExtensionCategory.isZero W).eq_of_src _ _
  rw [h]
  exact ExtensionCategory.cof_fromZero W _

end CategoryTheory.Waldhausen.QuotientRows
