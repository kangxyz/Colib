/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.SplitFiber
public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.FiltrationWeakMaps

/-! # The original split fiber has the literal constant initial filtration

Every initial interval [0,i+1] is sent to the original one-row interval
[0,1]. The original object, identity structural arrows and every original
morphism are therefore retained exactly, before nerves or realization.


Implementation provenance:
`Quillen/Waldhausen/Fibration/RelativeRows/FiberFiltration.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.RelativeRows
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)

/-- The canonical simplification rule for the underlying construction. -/
@[simp] theorem fiber_obj_initialInterval (n : SimplexCategory) (X : C) (i : Fin (n.len + 1)) :
    ((fiber N n).obj X).obj.obj.obj (interval 0 i.succ (Fin.zero_le _)) = X := rfl


/-- The canonical simplification rule for the underlying construction. -/
@[simp] theorem initialFiltration_fiber_map (n : SimplexCategory) (X : C)
    {i j : Fin (n.len + 1)} (f : i ⟶ j) :
    (initialFiltration ((fiber N n).obj X).obj).map f = 𝟙 X := rfl


/-- The canonical simplification rule for the underlying construction. -/
@[simp] theorem fiber_map_initialInterval (n : SimplexCategory) {X Y : C}
    (f : X ⟶ Y) (i : Fin (n.len + 1)) :
    ((fiber N n).map f).hom.hom.app (interval 0 i.succ (Fin.zero_le _)) = f := rfl


/-- The unchanged original fiber functor is sent to the actual constant-chain functor. -/
@[simp] theorem fiber_initialFiltrationFunctor (n : SimplexCategory) :
    fiber N n ⋙ initialFiltrationFunctor N n = Functor.const (Fin (n.len + 1)) := by
  apply CategoryTheory.Functor.ext (F := fiber N n ⋙ initialFiltrationFunctor N n)
    (G := Functor.const (Fin (n.len + 1))) (fun _ ↦ rfl)

end CategoryTheory.Waldhausen.Fibration.RelativeRows
