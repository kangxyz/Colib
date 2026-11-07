/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Grothendieck.EndofunctorTelescope

/-!
Adapted from `Quillen/Aglib/CategoryTheory/Grothendieck/TelescopeShift.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original functors
and coherence transformations.

# Index shift on the actual telescope of an endofunctor

The index shift and the genuine stagewise action of the defining endofunctor
are inverse up to specified natural-transformation homotopies. This concerns
right stabilization only; it makes no claim that arbitrary left translations
are homotopy equivalences.
-/

@[expose] public section
noncomputable section
open CategoryTheory
universe u v

namespace CategoryTheory.Grothendieck.EndofunctorTelescope
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] (T : C ⥤ C)

/-- The original successor on the stage index. -/
def successor : ℕ ⥤ ℕ where
  obj n := n + 1
  map f := homOfLE (Nat.add_le_add_right (leOfHom f) 1)

/-- Stationarity identifies the diagram with its successor restriction,
using the identity at every original fiber. -/
def shiftDiagramMap : diagram T ⟶ successor ⋙ diagram T where
  app _ := (𝟭 C).toCatHom
  naturality n m f := by
    change (iterate T (m - n)).toCatHom = (iterate T (m + 1 - (n + 1))).toCatHom
    rw [Nat.add_sub_add_right]

/-- Shift the original stage from `n` to `n+1`, leaving its fiber object unchanged. -/
def shift : Model T ⥤ Model T :=
  Grothendieck.map (shiftDiagramMap T) ⋙ Grothendieck.pre (diagram T) successor

/-- The actual stagewise action of the endofunctor defining the telescope. -/
def stabilization : Model T ⥤ Model T := map (𝟙 (T ⋙ T))

@[simp]
theorem shift_obj_base (X : Model T) : ((shift T).obj X).base = X.base + 1 := rfl

@[simp]
theorem shift_obj_fiber (X : Model T) : ((shift T).obj X).fiber = X.fiber := rfl

@[simp]
theorem stabilization_obj_base (X : Model T) : ((stabilization T).obj X).base = X.base := rfl

@[simp]
theorem stabilization_obj_fiber (X : Model T) :
    ((stabilization T).obj X).fiber = T.obj X.fiber := rfl

/-- Stabilization on each original stage is exactly the original functor. -/
theorem inclusion_stabilization (n : ℕ) :
    Grothendieck.ι (diagram T) n ⋙ stabilization T = T ⋙ Grothendieck.ι (diagram T) n :=
  inclusion_map (𝟙 (T ⋙ T)) n

/-- Index shift retains exactly the original next-stage inclusion. -/
theorem inclusion_shift (n : ℕ) :
    Grothendieck.ι (diagram T) n ⋙ shift T = Grothendieck.ι (diagram T) (n + 1) := by
  refine Functor.ext (fun _ ↦ rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  refine Grothendieck.ext (F := diagram T) _ _ rfl ?_
  simp [shift, shiftDiagramMap, Grothendieck.map, Grothendieck.pre,
    Grothendieck.ι, diagram, successor]

/-- Iteration commutes strictly with its defining endofunctor. -/
theorem iterate_comm (n : ℕ) : T ⋙ iterate T n = iterate T n ⋙ T := by
  change iterate T 1 ⋙ iterate T n = iterate T n ⋙ iterate T 1
  rw [← iterate_add, ← iterate_add, Nat.add_comm]

/-- The canonical commuting transformation contains only equality identifications. -/
theorem commuteIterate_stabilization (n : ℕ) :
    commuteIterate (𝟙 (T ⋙ T)) n = eqToHom (iterate_comm T n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply NatTrans.ext
    funext X
    simp [commuteIterate_succ, ih, eqToHom_map]

/-- The original stabilization arrow supplies the homotopy from the identity
to stabilization followed by index shift. -/
def stabilizationShiftUnit : 𝟭 (Model T) ⟶ stabilization T ⋙ shift T where
  app X :=
    { base := homOfLE (Nat.le_succ X.base)
      fiber := eqToHom (by
        change (iterate T (X.base + 1 - X.base)).obj X.fiber = T.obj X.fiber
        rw [Nat.add_sub_cancel_left]
        rfl) }
  naturality X Y f := by
    refine Grothendieck.ext (F := diagram T) _ _ (Subsingleton.elim _ _) ?_
    simp only [diagram, stabilization, map, Cat.of_α, Functor.toCatHom_toFunctor,
      Functor.comp_obj, shift, successor, homOfLE_leOfHom, shiftDiagramMap, Grothendieck.map,
      Functor.id_obj, Functor.comp_map, Cat.Hom.comp_toFunctor, Functor.id_map,
      Grothendieck.pre, Grothendieck.comp_base, homOfLE_comp, eqToHom_refl,
      Grothendieck.comp_fiber, Category.id_comp, eqToHom_map, Cat.Hom₂.eqToHom_toNatTrans,
      eqToHom_app, commuteIterate_stabilization, eqToHom_trans_assoc]
    have he : iterate T (Y.base + 1 - Y.base) = T := by
      rw [Nat.add_sub_cancel_left]
      rfl
    have hn := (eqToHom he).naturality f.fiber
    simp only [eqToHom_app] at hn
    rw [hn]
    simp only [← Category.assoc, eqToHom_trans]

/-- Index shift and the stagewise stabilization commute as actual functors. -/
theorem shift_stabilization : shift T ⋙ stabilization T = stabilization T ⋙ shift T := by
  refine Functor.ext (fun _ ↦ rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  refine Grothendieck.ext (F := diagram T) _ _ rfl ?_
  simp [shift, stabilization, map, shiftDiagramMap, Grothendieck.map,
    Grothendieck.pre, diagram, successor, commuteIterate_stabilization, eqToHom_map]

/-- The second composite has the same canonical stabilization homotopy. -/
def shiftStabilizationUnit : 𝟭 (Model T) ⟶ shift T ⋙ stabilization T :=
  stabilizationShiftUnit T ≫ eqToHom (shift_stabilization T).symm

end CategoryTheory.Grothendieck.EndofunctorTelescope
