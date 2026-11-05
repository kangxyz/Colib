/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.CategoryTheory.ExactCategory.Functor.Pullbacks
public import Colib.CategoryTheory.QConstruction.Functor

/-!
# Exact functors and Q-functoriality

The general exact functor and its selective pullback preservation are supplied
by the lower Colib modules. This module retains the Q-construction application.

## Implementation provenance

Adapted from `Quillen/CategoryTheory/ExactCategory/Functor.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Every declaration retains its original
functor, object and span maps, identity/composition equations, hypotheses and
independent universes. The mixed pullback preservation field is derived from
exactness and additivity rather than supplied as extra data.
-/
@[expose] public noncomputable section

open CategoryTheory.ExactCategory
universe v₁ v₂ v₃ u₁ u₂ u₃
open CategoryTheory CategoryTheory.Limits


namespace CategoryTheory.ExactCategory.ExactFunctor

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  {E : ExactStructure C} {E' : ExactStructure D} (F : ExactFunctor E E')

/-- Every exact functor satisfies the Q-compatibility conditions. The selective
pullback-preservation field is a theorem of exactness, not extra supplied data. -/
def toQCompatibleFunctor :
    QConstruction.CompatibleFunctor E.deflation E.inflation E'.deflation E'.inflation where
  toFunctor := F.toFunctor
  map_deflation := F.map_deflation
  map_inflation := F.map_inflation
  preserves_mixed i p _hi hp := F.preserves_pullback i p hp

/-- The Q-functor genuinely induced by an additive conflation-preserving functor. -/
def mapQ : QConstruction E.deflation E.inflation ⥤ QConstruction E'.deflation E'.inflation :=
  F.toQCompatibleFunctor.mapQ

@[simp]
theorem mapQ_obj_of (X : C) :
    F.mapQ.obj (QConstruction.of E.deflation E.inflation X) =
      QConstruction.of E'.deflation E'.inflation (F.toFunctor.obj X) := rfl

@[simp]
theorem mapQ_mkHom {X Y : C} (s : Span E.deflation E.inflation X Y) :
    F.mapQ.map (QConstruction.mkHom E.deflation E.inflation s) =
      QConstruction.mkHom E'.deflation E'.inflation (F.toQCompatibleFunctor.mapSpan s) := rfl

/-- Exact-functor identities induce identity Q-functors. -/
@[simp]
theorem mapQ_id (E : ExactStructure C) :
    (id E).mapQ = 𝟭 (QConstruction E.deflation E.inflation) := by
  refine Functor.hext ?_ ?_
  · intro X
    rfl
  · rintro X Y ⟨s⟩
    rfl

/-- Exact-functor composition is respected by the Q-construction. -/
@[simp]
theorem mapQ_comp {T : Type u₃} [Category.{v₃} T] [Preadditive T] [HasFiniteBiproducts T]
    {E'' : ExactStructure T} (G : ExactFunctor E' E'') :
    (F.comp G).mapQ = F.mapQ ⋙ G.mapQ := by
  refine Functor.hext ?_ ?_
  · intro X
    rfl
  · rintro X Y ⟨s⟩
    rfl

end CategoryTheory.ExactCategory.ExactFunctor

attribute [colib_tag "COL-0037",
  colib_ref "WeibelKBook"
    "IV, paragraph following Definition 6.3, induced Q-functor clause" "clause"
    "The induced Q-functor maps actual objects and spans and respects identity and composition"]
  CategoryTheory.ExactCategory.ExactFunctor.mapQ
  CategoryTheory.ExactCategory.ExactFunctor.mapQ_mkHom
  CategoryTheory.ExactCategory.ExactFunctor.mapQ_id
  CategoryTheory.ExactCategory.ExactFunctor.mapQ_comp

attribute [colib_ref "BuhlerExactCategories" "Proposition 5.2, pullback clause" "ingredient"
    "Exactness derives the selective pullback preservation required for Q-compatibility"]
  CategoryTheory.ExactCategory.ExactFunctor.toQCompatibleFunctor
