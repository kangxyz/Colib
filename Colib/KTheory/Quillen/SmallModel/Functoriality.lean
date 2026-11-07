/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.SmallModel.Functoriality
public import Colib.KTheory.Quillen.SmallModel.Exact
public import Colib.KTheory.Quillen.Map.NaturalIso

/-!
# Functoriality of small-model K-theory

The chosen small-model equivalences provide natural identity and composition
comparisons. Natural-isomorphism invariance of the zero-normalized K-map
turns these comparisons into strict identity and composition laws on SmallK.
No comparison with an out-of-universe realization is required.

## Implementation provenance

Adapted from `Quillen/CategoryTheory/SmallModel/Functoriality.lean` at
Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. These are equalities
of the existing canonical `smallKMap` at the original small universe.
-/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe w v₁ v₂ v₃ u₁ u₂ u₃
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ExactCategory.ExactFunctor

variable {C : Type u₁} {D : Type u₂} {T : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} T]
  [Preadditive C] [Preadditive D] [Preadditive T]
  [HasFiniteBiproducts C] [HasFiniteBiproducts D] [HasFiniteBiproducts T]
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D] [EssentiallySmall.{w} T]
  {EC : ExactStructure C} {ED : ExactStructure D} {ET : ExactStructure T}

/-- The actual small-model K-map is invariant under underlying natural
isomorphisms, even when the original categories have different universes. -/
theorem smallKMap_eq_of_natIso {F G : ExactFunctor EC ED}
    (e : F.toFunctor ≅ G.toFunctor) (n : ℕ) : F.smallKMap n = G.smallKMap n :=
  KMap_eq_of_natIso (smallModelNatIso e) n

/-- Small-model K-theory preserves identity exact functors. -/
@[simp]
theorem smallKMap_id (E : ExactStructure C) (n : ℕ) :
    (CategoryTheory.ExactCategory.ExactFunctor.id E).smallKMap n = MonoidHom.id (E.SmallK n) := by
  exact (KMap_eq_of_natIso (smallModelIdIso E) n).trans (KMap_id E.smallModel n)

/-- Small-model K-theory preserves composition of actual exact functors. -/
@[simp]
theorem smallKMap_comp (F : ExactFunctor EC ED) (G : ExactFunctor ED ET) (n : ℕ) :
    (F.comp G).smallKMap n = (G.smallKMap n).comp (F.smallKMap n) := by
  exact (KMap_eq_of_natIso (smallModelCompIso F G) n).trans
    (KMap_comp F.smallModel G.smallModel n)

end CategoryTheory.ExactCategory.ExactFunctor
