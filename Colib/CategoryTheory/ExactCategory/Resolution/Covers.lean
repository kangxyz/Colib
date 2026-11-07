/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Resolution.Finite

/-! Adapted from `Quillen/Aglib/CategoryTheory/ExactCategory/Resolution/Covers.lean`
at pinned Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd.
This module supplies finite-resolution prerequisites, not the Resolution theorem. -/

/-!
# Admissible resolving covers

The objects are actual admissible epimorphisms onto a fixed object, with
source in the resolving subcategory. Morphisms are admissible epimorphisms
commuting with the augmentations. This extracted prerequisite does not include
the pullback contraction.
-/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ExactCategory.Resolution
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (P : ObjectProperty C) (M : C)

/-- An actual admissible epimorphism from a resolving object. -/
structure Cover where
  /-- The resolving source object of the cover, required to satisfy `P`. -/
  obj : C
  property : P obj
  /-- The admissible epimorphism from the resolving source onto `M`. -/
  hom : obj ⟶ M
  admissible : E.deflation hom

namespace Cover
variable {E P M}

/-- Cover comparisons are themselves admissible epimorphisms. -/
@[ext] structure Hom (X Y : Cover E P M) where
  /-- The admissible epimorphism between cover sources that commutes with their maps to `M`. -/
  hom : X.obj ⟶ Y.obj
  admissible : E.deflation hom
  w : hom ≫ Y.hom = X.hom

instance : Category (Cover E P M) where
  Hom := Hom
  id X := ⟨𝟙 X.obj, E.deflation_id _, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, E.deflation_comp _ _ f.admissible g.admissible,
    by rw [Category.assoc, g.w, f.w]⟩
  id_comp _ := Hom.ext (by simp)
  comp_id _ := Hom.ext (by simp)
  assoc _ _ _ := Hom.ext (by simp [Category.assoc])

@[simp] lemma id_hom (X : Cover E P M) : (𝟙 X : X ⟶ X).hom = 𝟙 X.obj := rfl
@[simp] lemma comp_hom {X Y Z : Cover E P M} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

/-- The augmentation of an actual finite resolution is an admissible cover. -/
def ofFiniteResolution (R : E.FiniteResolution P M) : Cover E P M :=
  let t := R.presentation
  ⟨t.1, t.2.2.1, t.2.1, t.2.2.2⟩

/-- Objectwise finite resolutions provide a resolving cover of each object. -/
theorem nonempty_of_resolutionHypothesis (h : E.ResolutionHypothesis P) :
    Nonempty (Cover E P M) := by
  obtain ⟨R⟩ := h M
  exact ⟨ofFiniteResolution R⟩

end Cover
end CategoryTheory.ExactCategory.Resolution
