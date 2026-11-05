/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.CategoryTheory.ExactCategory.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Exact additive functors

An exact functor between chosen exact structures is an additive functor preserving
conflations. Identity and composition retain this property, and exact functors send
admissible monomorphisms and epimorphisms to admissible monomorphisms and epimorphisms.

This is exactness with respect to the selected conflations, not preservation of all
finite limits and colimits. In particular, it does not require the categories to be
abelian or to have arbitrary kernels, cokernels, pullbacks or pushouts.

## Implementation provenance

Extracted from `Aglib/CategoryTheory/ExactCategory/Functor.lean` at Aglib commit
`2c34f185fa859e862661f939cd216b07bcccfb26`. The structure, identity, composition and
admissibility lemmas retain the source hypotheses, universes and underlying functors.
The matrix-kernel argument and preservation of admissible pullbacks belong to a later
module and are not dependencies of this basic interface.
-/

@[expose] public noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive

namespace CategoryTheory.ExactCategory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]

/-- An exact functor is an additive functor preserving the specified conflations. -/
structure ExactFunctor (E : ExactStructure C) (E' : ExactStructure D) where
  /-- The underlying functor from the source exact category to the target exact category. -/
  toFunctor : C ⥤ D
  /-- The underlying functor is additive. -/
  [additive : toFunctor.Additive]
  /-- The underlying functor preserves the chosen conflations. -/
  map_conflation : ∀ (S : ShortComplex C), E.conflation S →
    E'.conflation (S.map toFunctor)

attribute [instance] ExactFunctor.additive


namespace ExactFunctor

/-- The identity functor is exact. -/
def id (E : ExactStructure C) : ExactFunctor E E where
  toFunctor := 𝟭 C
  map_conflation _ hs := hs

/-- The composite of exact functors is exact. -/
def comp {E : ExactStructure C} {E' : ExactStructure D}
    {T : Type u₃} [Category.{v₃} T] [Preadditive T] [HasFiniteBiproducts T]
    {E'' : ExactStructure T} (F : ExactFunctor E E') (G : ExactFunctor E' E'') :
    ExactFunctor E E'' where
  toFunctor := F.toFunctor ⋙ G.toFunctor
  map_conflation S hs := G.map_conflation _ (F.map_conflation S hs)

variable {E : ExactStructure C} {E' : ExactStructure D} (F : ExactFunctor E E')

/-- Exact functors preserve admissible epimorphisms. -/
lemma map_deflation {X Y : C} (p : X ⟶ Y) (hp : E.deflation p) :
    E'.deflation (F.toFunctor.map p) := by
  obtain ⟨K, i, h, hs⟩ := hp
  exact E'.deflation_of_conflation (F.map_conflation _ hs)

/-- Exact functors preserve admissible monomorphisms. -/
lemma map_inflation {X Y : C} (i : X ⟶ Y) (hi : E.inflation i) :
    E'.inflation (F.toFunctor.map i) := by
  obtain ⟨K, p, h, hs⟩ := hi
  exact E'.inflation_of_conflation (F.map_conflation _ hs)

end ExactFunctor

end CategoryTheory.ExactCategory

attribute [colib_tag "COL-0023",
  colib_ref "BuhlerExactCategories" "Definition 5.1" "adaptation"
    "Additive functors preserving the specified conflations"]
  CategoryTheory.ExactCategory.ExactFunctor

attribute [colib_tag "COL-0023"]
  CategoryTheory.ExactCategory.ExactFunctor.id
  CategoryTheory.ExactCategory.ExactFunctor.comp
