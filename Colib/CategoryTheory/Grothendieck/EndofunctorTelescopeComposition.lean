/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Grothendieck.EndofunctorTelescopeNaturality

/-!
Adapted from `Quillen/Aglib/CategoryTheory/Grothendieck/EndofunctorTelescopeComposition.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original functors
and coherence transformations.
 # Composition of actual telescope maps -/
@[expose] public section
open CategoryTheory
universe u v
namespace CategoryTheory.Grothendieck.EndofunctorTelescope
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] {L M T : C ⥤ C}

/-- Compose the two specified commutation transformations in their original order. -/
def composeStep (a : L ⋙ T ⟶ T ⋙ L) (b : M ⋙ T ⟶ T ⋙ M) :
    (L ⋙ M) ⋙ T ⟶ T ⋙ (L ⋙ M) :=
  Functor.whiskerLeft L b ≫ Functor.whiskerRight a M

theorem commuteIterate_composeStep (a : L ⋙ T ⟶ T ⋙ L) (b : M ⋙ T ⟶ T ⋙ M)
    (n : ℕ) (X : C) :
    (commuteIterate (composeStep a b) n).app X =
      (commuteIterate b n).app (L.obj X) ≫ M.map ((commuteIterate a n).app X) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [commuteIterate_succ, ih]
    simp only [commuteIterate_succ, Functor.map_comp, composeStep, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
    have hb := b.naturality ((commuteIterate a n).app X)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hb
    rw [← Category.assoc (T.map (M.map ((commuteIterate a n).app X))), hb]
    simp only [Category.assoc]

/-- Composition agrees with the originally defined Grothendieck functors. -/
theorem map_composeStep (a : L ⋙ T ⟶ T ⋙ L) (b : M ⋙ T ⟶ T ⋙ M) :
    map (composeStep a b) = map a ⋙ map b := by
  refine Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  refine Grothendieck.ext _ _ ?_ ?_
  · rfl
  dsimp [map]
  rw [commuteIterate_composeStep]
  simp only [Functor.map_comp, Category.assoc, Category.id_comp]

@[simp] theorem commuteIterate_identity (T : C ⥤ C) (n : ℕ) (X : C) :
    (commuteIterate (L := 𝟭 C) (𝟙 T) n).app X = 𝟙 _ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [commuteIterate_succ, ih, Functor.map_id, NatTrans.id_app, Category.id_comp]
    rfl

/-- The identity functor induces precisely the identity telescope map. -/
theorem map_identity (T : C ⥤ C) : map (L := 𝟭 C) (𝟙 T) = 𝟭 (Model T) := by
  refine Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  refine Grothendieck.ext _ _ ?_ ?_
  · rfl
  dsimp [map]
  rw [commuteIterate_identity]
  exact (Category.id_comp ((𝟙 _) ≫ f.fiber)).trans (Category.id_comp f.fiber)

end CategoryTheory.Grothendieck.EndofunctorTelescope
