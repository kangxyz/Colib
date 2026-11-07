/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Grothendieck

/-! # Identity and composition of the original Grothendieck fiber transitions -/

/-!
Implementation provenance: adapted from `Quillen/Aglib/CategoryTheory/Grothendieck/FiberTransitions.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original functors,
comparison maps, homotopies, hypotheses and universes are retained.
-/

@[expose] public section
open CategoryTheory
universe u v w t
namespace CategoryTheory.Grothendieck
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] (F : C ⥤ Cat.{w, t})

/-- The identity transition is the actual functorial identity identification. -/
theorem fiberTransition_id (c : C) :
    ιNatTrans (F := F) (𝟙 c) = eqToHom (by rw [F.map_id]; rfl) := by
  apply NatTrans.ext
  funext X
  simp only [eqToHom_app]
  refine Grothendieck.ext _ _ ?_ ?_
  · simp only [ιNatTrans, base_eqToHom, eqToHom_refl]
    rfl
  · simp only [ιNatTrans, fiber_eqToHom, Category.comp_id]

/-- The composite transition retains exactly the original diagram composition identification. -/
theorem fiberTransition_comp {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
    ιNatTrans (F := F) (f ≫ g) =
      ιNatTrans (F := F) f ≫ Functor.whiskerLeft (F.map f).toFunctor (ιNatTrans (F := F) g) ≫
        eqToHom (by rw [F.map_comp]; rfl) := by
  apply NatTrans.ext
  funext X
  simp only [NatTrans.comp_app, eqToHom_app]
  refine Grothendieck.ext _ _ ?_ ?_
  · simp [ιNatTrans, base_eqToHom]
  · simp [ιNatTrans, fiber_eqToHom, Grothendieck.comp_fiber]

/-- Every genuine Grothendieck arrow factors through its original transition
and its original vertical fiber arrow. -/
theorem fiberTransition_factorization {X Y : Grothendieck F} (f : X ⟶ Y) :
    (ιNatTrans (F := F) f.base).app X.fiber ≫ (ι F Y.base).map f.fiber = f := by
  refine Grothendieck.ext _ _ ?_ ?_
  · simp [ιNatTrans, ι]
  · simp [ιNatTrans, ι, Grothendieck.comp_fiber]

/-- Over a thin base, an arrow with an invertible original fiber map is epic.
This uses only the specified fiber map, not groupoid structure on the fibers. -/
theorem epi_of_fiber_isIso [Quiver.IsThin C] {X Y : Grothendieck F} (f : X ⟶ Y)
    [IsIso f.fiber] : Epi f where
  left_cancellation {Z} g h w := by
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

/-- In particular, every original fiber transition is epic over a thin base. -/
theorem fiberTransition_epi [Quiver.IsThin C] {a b : C} (f : a ⟶ b) (X : F.obj a) :
    Epi ((ιNatTrans (F := F) f).app X) := by
  let : IsIso ((ιNatTrans (F := F) f).app X).fiber := by
    change IsIso (𝟙 _)
    infer_instance
  exact epi_of_fiber_isIso F _

end CategoryTheory.Grothendieck
