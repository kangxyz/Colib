/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.Groupoid

/-!
Adapted from `Quillen/Aglib/CategoryTheory/Grothendieck/GroupoidRightFactors.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual objects,
functors, coefficient universes and comparison maps.

# Actual right division in sequential Grothendieck constructions of groupoids -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace CategoryTheory.Grothendieck
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable (F : ℕ ⥤ Cat.{u, u}) [∀ n, IsGroupoid (F.obj n)]

/-- A later-target arrow divides uniquely through an earlier-target arrow
using the inverse of its original groupoid fiber component. -/
def rightFactor {x y z : Grothendieck F} (f : x ⟶ y) (g : x ⟶ z)
    (h : y.base ≤ z.base) : y ⟶ z where
  base := homOfLE h
  fiber := inv ((F.map (homOfLE h)).toFunctor.map f.fiber) ≫
    eqToHom (by
      rw [← Cat.Hom.comp_obj, ← F.map_comp]
      congr 2) ≫ g.fiber

/-- The actual right factor solves the original triangle exactly. -/
theorem rightFactor_fac {x y z : Grothendieck F} (f : x ⟶ y) (g : x ⟶ z)
    (h : y.base ≤ z.base) : f ≫ rightFactor F f g h = g := by
  refine Grothendieck.ext _ _ (Subsingleton.elim _ _) ?_
  simp [Grothendieck.comp_fiber, rightFactor]

/-- Every original Grothendieck arrow is epic when the indexing category is thin
and the fiber categories are groupoids. -/
instance hom_epi {x y : Grothendieck F} (f : x ⟶ y) : Epi f where
  left_cancellation {z} g h w := by
    cases g with | mk gb gf =>
      cases h with | mk hb hf =>
        obtain rfl : gb = hb := Subsingleton.elim _ _
        have hw := Grothendieck.congr w
        simp only [Grothendieck.comp_fiber, eqToHom_refl, Category.id_comp] at hw
        have he : gf = hf := by
          apply (cancel_epi ((F.map gb).toFunctor.map f.fiber)).mp
          exact (cancel_epi (eqToHom _)).mp hw
        subst hf
        rfl

end CategoryTheory.Grothendieck
