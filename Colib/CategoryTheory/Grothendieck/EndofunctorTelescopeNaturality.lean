/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Grothendieck.EndofunctorTelescope

/-!
Adapted from `Quillen/Aglib/CategoryTheory/Grothendieck/EndofunctorTelescopeNaturality.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original functors
and coherence transformations.
 # Natural transformations between genuine telescope maps -/
@[expose] public section
open CategoryTheory
universe u v
namespace CategoryTheory.Grothendieck.EndofunctorTelescope
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] {L M T : C ⥤ C}
variable (a : L ⋙ T ⟶ T ⋙ L) (b : M ⋙ T ⟶ T ⋙ M) (η : L ⟶ M)
variable (h : ∀ X, T.map (η.app X) ≫ b.app X = a.app X ≫ η.app (T.obj X))

include h in
theorem commuteIterate_naturality (n : ℕ) (X : C) :
    (iterate T n).map (η.app X) ≫ (commuteIterate b n).app X =
      (commuteIterate a n).app X ≫ η.app ((iterate T n).obj X) := by
  induction n with
  | zero => simp [commuteIterate]
  | succ n ih =>
    simp only [iterate_succ, Functor.comp_map, commuteIterate_succ]
    rw [← Category.assoc, ← T.map_comp, ih, T.map_comp, Category.assoc, h]
    simp only [Category.assoc, Functor.comp_obj]

theorem iterate_map_of_eq_zero (n : ℕ) (hn : n = 0) {X Y : C} (f : X ⟶ Y) :
    (iterate T n).map f = eqToHom (by subst n; rfl) ≫ f ≫
      eqToHom (by subst n; rfl) := by
  subst n
  simp

include h in
/-- A compatible natural transformation induces its original stagewise map on the telescope. -/
def mapNatTrans : map a ⟶ map b where
  app X := (Grothendieck.ι (diagram T) X.base).map (η.app X.fiber)
  naturality {X Y} f := by
    refine Grothendieck.ext _ _ ?_ ?_
    · apply Subsingleton.elim
    dsimp [Grothendieck.comp_fiber, Grothendieck.ι, map, diagram]
    change ((𝟙 _) ≫ eqToHom _ ≫ (iterate T (Y.base - Y.base)).map
      ((commuteIterate a (Y.base - X.base)).app X.fiber ≫ L.map f.fiber) ≫
      eqToHom _ ≫ η.app Y.fiber) =
      eqToHom _ ≫ (iterate T (Y.base - X.base)).map (eqToHom _ ≫ η.app X.fiber) ≫
      (commuteIterate b (Y.base - X.base)).app X.fiber ≫ M.map f.fiber
    rw [iterate_map_of_eq_zero _ (Nat.sub_self _)]
    simp only [Category.assoc, Category.id_comp, Functor.map_comp, eqToHom_map]
    simp only [← Category.assoc, eqToHom_trans]
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id, Category.assoc]
    rw [← Category.assoc ((iterate T (Y.base - X.base)).map (η.app X.fiber)),
      commuteIterate_naturality a b η h]
    simp only [Category.assoc]
    rw [η.naturality]

/-- A compatible original natural isomorphism gives an isomorphism of telescope maps. -/
def mapNatIso (e : L ≅ M)
    (he : ∀ X, T.map (e.hom.app X) ≫ b.app X = a.app X ≫ e.hom.app (T.obj X)) :
    map a ≅ map b :=
  NatIso.ofComponents
    (fun X => (Grothendieck.ι (diagram T) X.base).mapIso (e.app X.fiber))
    (fun f => (mapNatTrans a b e.hom he).naturality f)

end CategoryTheory.Grothendieck.EndofunctorTelescope
