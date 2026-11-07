/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.ExactFunctor

/-!
# Small Waldhausen categories and exact functors

The canonical bundled category retains all exact functors, without strict
chosen-zero preservation. Its definition is extracted unchanged from the
original K-functor owner. Strict chosen-zero preservation is a multiplicative
morphism property, so Mathlib's wide subcategory supplies its restricted category.
-/
@[expose] public section

noncomputable section
open CategoryTheory
universe u
namespace CategoryTheory.Waldhausen

/-- A small category equipped with its original Waldhausen structure and chosen zero. -/
structure SmallWaldhausenCategory : Type (u + 1) where
  /-- The original object type in the selected universe. -/
  Obj : Type u
  [category : SmallCategory Obj]
  /-- The original cofibrations, weak equivalences and zero-object data. -/
  waldhausen : Structure Obj

attribute [instance] SmallWaldhausenCategory.category

namespace SmallWaldhausenCategory

/-- All actual exact functors are retained, without strict chosen-zero preservation. -/
@[ext] structure Hom (C D : SmallWaldhausenCategory.{u}) where
  /-- The original underlying functor. -/
  toFunctor : C.Obj ⥤ D.Obj
  /-- The original structural exactness properties. -/
  isExact : IsExact C.waldhausen.cof C.waldhausen.weq
    D.waldhausen.cof D.waldhausen.weq toFunctor

instance : Category.{u} SmallWaldhausenCategory.{u} where
  Hom := Hom
  id C := ⟨𝟭 C.Obj, IsExact.id _ _⟩
  comp F G := ⟨F.toFunctor ⋙ G.toFunctor, F.isExact.comp G.isExact⟩
  id_comp F := by apply Hom.ext; rfl
  comp_id F := by apply Hom.ext; rfl
  assoc F G H := by apply Hom.ext; rfl

/-- Exact functors preserving the specified zero object by equality. -/
def preservesZero : MorphismProperty SmallWaldhausenCategory.{u} :=
  fun C D F ↦ F.toFunctor.obj C.waldhausen.zero = D.waldhausen.zero

instance : preservesZero.IsMultiplicative where
  id_mem _ := rfl
  comp_mem F G hF hG := by
    change G.toFunctor.obj (F.toFunctor.obj _) = _
    rw [hF, hG]

end SmallWaldhausenCategory
end CategoryTheory.Waldhausen
