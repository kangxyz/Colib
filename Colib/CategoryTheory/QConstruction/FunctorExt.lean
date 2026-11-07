/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.QConstruction.Functor

/-! # Extensionality of compatible Q-construction functors

Extracted from AuxiliaryDiagram at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd.
The native compatible functor is determined by its ordinary functor.
-/

@[expose] public section
universe v₁ v₂ u₁ u₂
namespace CategoryTheory

/-- Compatible functors are determined by their underlying ordinary functor. -/
theorem QConstruction.CompatibleFunctor.ext_toFunctor
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    {W V : MorphismProperty C} {W' V' : MorphismProperty D}
    {F G : QConstruction.CompatibleFunctor W V W' V'} (h : F.toFunctor = G.toFunctor) : F = G := by
  cases F
  cases G
  cases h
  rfl

end CategoryTheory
