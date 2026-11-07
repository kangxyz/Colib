/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.EqToHom

/-!
# Transport

Component formula for transporting the source functor of a natural iso.
-/

@[expose] public section

noncomputable section
open CategoryTheory
universe u v w z
namespace CategoryTheory

/-- Component formula for transporting the source functor of a natural iso. -/
theorem natIso_transport_hom_app {D : Type u} [Category.{v} D]
    {E : Type w} [Category.{z} E] {F G H : D ⥤ E} (h : F = G) (e : F ≅ H) (x : D) :
    (cast (congrArg (fun K : D ⥤ E => K ≅ H) h) e).hom.app x =
      eqToHom (congrArg (fun K : D ⥤ E => K.obj x) h.symm) ≫
      e.hom.app x := by
  cases h
  simp

/-- Object equality transport along a specified parameter equality. -/
theorem isoFamily_parameter_transport {B : Type u} {D : Type v} [Category.{w} D]
    (obj : B → D) (target : D) (γ : ∀ b, obj b ≅ target)
    {x y : B} (h : x = y) (he : obj x = obj y) :
    eqToHom he ≫ (γ y).hom = (γ x).hom := by
  subst y
  simp

end CategoryTheory
