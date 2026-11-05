/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import StacksCore.CategoryTheory.Abelian.SerreClass.Localization

/-!
# The exact functor of an additive Serre localization

Adapted from `Aglib/CategoryTheory/Abelian/SerreClass/Exact.lean` at Aglib commit
`2c34f185fa859e862661f939cd216b07bcccfb26`. The underlying functor, standard exact
structures and independent source/target universes are retained. Preservation of
conflations is supplied by the pinned Stacks short-exact-sequence theorem.
-/

@[expose] public noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.ExactCategory.ExactFunctor

attribute [local instance] Abelian.hasFiniteBiproducts

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] (P : ObjectProperty C) [P.IsSerreClass]
  (L : C ⥤ D) [L.IsLocalization P.isoModSerre] [L.Additive]

/-- An additive Serre localization preserves the standard abelian conflations. -/
def serreLocalization : ExactFunctor (abelianExactStructure C) (abelianExactStructure D) where
  toFunctor := L
  map_conflation _ hS := ObjectProperty.SerreClassLocalization.shortExact_map L P hS

end CategoryTheory.ExactCategory.ExactFunctor

attribute [colib_tag "COL-0027",
  stacks 02MS "exact quotient functor clause, packaged for canonical abelian exact structures",
  colib_ref "BuhlerExactCategories" "Definition 5.1" "adaptation"
    "The actual additive Serre localization functor preserves the canonical conflations"]
  CategoryTheory.ExactCategory.ExactFunctor.serreLocalization
