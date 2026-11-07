/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.Subdivision.Action

/-!
# Functoriality of the actual subdivision category

## Implementation provenance

Adapted from `Quillen/Aglib/CategoryTheory/Subdivision/Functor.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, chosen paths, and original
proof hypotheses are retained under native ownership.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory Opposite
namespace CategoryTheory.Subdivision
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]

/-- Apply the original functor to both sides of every subdivision factorization. -/
def map (F : C ⥤ D) : Subdivision C ⥤ Subdivision D where
  obj X := of (F.map X.fiber.unop.hom)
  map f := mkHom (F.map (domainMap f)) (F.map f.base) (by
    rw [← F.map_comp, ← F.map_comp, factorization])
  map_id X := by
    apply hom_ext <;> simp [mkHom, domainMap, of]
  map_comp f g := by
    apply hom_ext <;> simp [mkHom, domainMap, of, Grothendieck.comp_fiber]

/-- Mapping the object represented by an arrow retains its original mapped arrow. -/
@[simp] theorem map_obj_of (F : C ⥤ D) {A B : C} (i : A ⟶ B) :
    (map F).obj (of i) = of (F.map i) := rfl

/-- The base coordinate is the image of the original base coordinate. -/
@[simp] theorem map_base (F : C ⥤ D) {X Y : Subdivision C} (f : X ⟶ Y) :
    ((map F).map f).base = F.map f.base := rfl

/-- The original domain map is preserved by the subdivision functor. -/
@[simp] theorem map_domainMap (F : C ⥤ D) {X Y : Subdivision C} (f : X ⟶ Y) :
    domainMap ((map F).map f) = F.map (domainMap f) := rfl

/-- The actual middle-object projection is preserved strictly. -/
theorem map_codomain (F : C ⥤ D) : map F ⋙ codomain = codomain ⋙ F := by
  refine Functor.ext (fun _ ↦ rfl) ?_
  intro X Y f
  simp
  rfl

end CategoryTheory.Subdivision
