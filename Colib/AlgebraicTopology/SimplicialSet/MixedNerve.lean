/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.CategoryTheory.Functor.Currying

/-! # Nerve maps and homotopies with independent hom universes

Adapted from `Quillen/Waldhausen/QuillenComparison/MixedNerve.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Both nerves are the existing native
category nerves; only the unnecessary equality of hom universes is removed.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial
universe u v w

namespace CategoryTheory.MixedNerve

variable {C D : Type (max u v w)} [Category.{v} C] [Category.{w} D]

/-- Postcomposition on nerves, retaining the possibly different hom universes. -/
def nerveMap (F : C ⥤ D) : nerve C ⟶ nerve D where
  app _ := ↾fun G ↦ G ⋙ F
  naturality _ _ _ := rfl

/-- The categorical-interval cylinder has the same explicit formula in mixed universes. -/
def cylinder {F G : C ⥤ D} (α : F ⟶ G) : nerve C ⊗ Δ[1] ⟶ nerve D where
  app _ := ↾fun z ↦ (z.2.down.toOrderHom.monotone.functor.prod' z.1) ⋙
    Functor.uncurry.obj (ComposableArrows.mk₁ α)
  naturality _ _ _ := rfl

@[simp]
theorem cylinder_zero {F G : C ⥤ D} (α : F ⟶ G) :
    SSet.ι₀ ≫ cylinder.{u, v, w} α = nerveMap.{u, v, w} F := by
  ext n z
  change ((Functor.const (Fin (n.unop.len + 1))).obj (0 : Fin 2)).prod' z ⋙
    Functor.uncurry.obj (ComposableArrows.mk₁ α) = z ⋙ F
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro i j f
  simp [Functor.uncurry, ComposableArrows.mk₁, Functor.prod']

@[simp]
theorem cylinder_one {F G : C ⥤ D} (α : F ⟶ G) :
    SSet.ι₁ ≫ cylinder.{u, v, w} α = nerveMap.{u, v, w} G := by
  ext n z
  change ((Functor.const (Fin (n.unop.len + 1))).obj (1 : Fin 2)).prod' z ⋙
    Functor.uncurry.obj (ComposableArrows.mk₁ α) = z ⋙ G
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro i j f
  simp [Functor.uncurry, ComposableArrows.mk₁, Functor.prod']

/-- Natural transformations give actual simplicial homotopies. -/
def homotopy {F G : C ⥤ D} (α : F ⟶ G) :
    SSet.Homotopy (nerveMap.{u, v, w} F) (nerveMap.{u, v, w} G) where
  h := cylinder.{u, v, w} α
  h₀ := cylinder_zero.{u, v, w} α
  h₁ := cylinder_one.{u, v, w} α
  rel := by ext n z; exact z.1.property.elim

end CategoryTheory.MixedNerve
