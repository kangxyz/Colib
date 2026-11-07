/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Subdivision.Basic

/-!
Implementation provenance:
`Quillen/Aglib/CategoryTheory/Subdivision/Initial.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Subdivision and an initial object

Replacing the domain of an arrow by the specified initial object gives an
actual endofunctor. Both the identity and the constant identity-arrow functor
map naturally into it. The category itself need not have an initial object.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe v u

namespace CategoryTheory.Subdivision

variable {C : Type u} [Category.{v} C] {z : C} (hz : IsInitial z)

/-- Send an object to its unique arrow from the specified initial object. -/
def initialArrowFunctor : C ⥤ Subdivision C where
  obj B := of (hz.to B)
  map f := mkHom (𝟙 z) f (hz.hom_ext _ _)
  map_id B := by simp
  map_comp f g := by
    rw [mkHom_comp]
    simp

/-- Replace only the domain of a subdivision object by the initial object. -/
def initialRaise : Subdivision C ⥤ Subdivision C := codomain ⋙ initialArrowFunctor hz

/-- The original domain map gives a transformation from the identity. -/
def identityToInitialRaise : 𝟭 (Subdivision C) ⟶ initialRaise hz where
  app X := mkHom (hz.to X.fiber.unop.left) (𝟙 X.base) (hz.hom_ext _ _)
  naturality X Y f := by
    apply Grothendieck.ext _ _ (by simp [initialRaise, initialArrowFunctor, mkHom, codomain])
    apply Quiver.Hom.unop_inj
    apply Over.OverMorphism.ext
    exact hz.hom_ext _ _

/-- The original codomain map gives a transformation from the constant identity arrow. -/
def constantToInitialRaise : (Functor.const (Subdivision C)).obj (of (𝟙 z)) ⟶
    initialRaise hz where
  app X := mkHom (𝟙 z) (hz.to X.base) (by simp [codomain])
  naturality X Y f := by
    apply Grothendieck.ext _ _ (hz.hom_ext _ _)
    apply Quiver.Hom.unop_inj
    apply Over.OverMorphism.ext
    exact hz.hom_ext _ _
end CategoryTheory.Subdivision
