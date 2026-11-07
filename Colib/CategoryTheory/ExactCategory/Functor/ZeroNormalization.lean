/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.CategoryTheory.Functor.Rebase
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-! # Canonical zero normalization of exact functors

Adapted from `Quillen/Waldhausen/QuillenComparison/ZeroNormalization.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original functors,
canonical zero isomorphisms and based homotopies.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
universe v u v₁ v₂ u₁ u₂

namespace CategoryTheory.ExactCategory.ExactFunctor
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D} (F : ExactFunctor EC ED)

/-- Normalize the original functor at the chosen zero, transporting additivity
and conflations through the actual component isomorphisms. -/
def zeroNormalized : ExactFunctor EC ED := by
  let G := rebaseFunctor F.toFunctor (0 : C) (0 : D) F.toFunctor.mapZeroObject
  let e : F.toFunctor ≅ G := rebaseFunctorIso F.toFunctor _ _ _
  letI : G.Additive := CategoryTheory.Functor.additive_of_iso e
  exact {
    toFunctor := G
    map_conflation S hS := ED.iso_closed (S.mapNatIso e) (F.map_conflation S hS) }

/-- This is the same objectwise rebasing used by based Waldhausen maps. -/
theorem zeroNormalized_toFunctor : F.zeroNormalized.toFunctor =
    rebaseFunctor F.toFunctor (0 : C) (0 : D) F.toFunctor.mapZeroObject := rfl

/-- The comparison is a genuine natural isomorphism of the original functors. -/
def zeroNormalizedIso : F.toFunctor ≅ F.zeroNormalized.toFunctor :=
  rebaseFunctorIso F.toFunctor (0 : C) (0 : D) F.toFunctor.mapZeroObject

/-- The normalized exact functor preserves the chosen zero strictly. -/
theorem zeroNormalized_obj_zero : F.zeroNormalized.toFunctor.obj (0 : C) = (0 : D) :=
  rebaseFunctor_obj_base F.toFunctor _ _ _

end CategoryTheory.ExactCategory.ExactFunctor
