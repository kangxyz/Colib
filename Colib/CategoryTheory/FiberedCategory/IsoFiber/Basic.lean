/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
Implementation provenance:
`Quillen/Aglib/CategoryTheory/FiberedCategory/IsoFiber/Basic.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# The isomorphism fiber of a functor

The isomorphism fiber is the full subcategory of the structured comma category
on invertible structure maps. It retains the specified isomorphism to the
base object and does not require a strict equality of projected objects.
-/

@[expose] public section
universe u v u' v'
open CategoryTheory
namespace CategoryTheory
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- Objects above the base object equipped with an invertible structure map. -/
def isoFiberProperty (F : C ⥤ D) (b : D) : ObjectProperty (StructuredArrow b F) :=
  fun X ↦ IsIso X.hom

/-- The isomorphism fiber, oriented for a fibered functor. -/
abbrev IsoFiber (F : C ⥤ D) (b : D) := (isoFiberProperty F b).FullSubcategory

namespace IsoFiber
variable (F : C ⥤ D) (b : D)

/-- Retain the actual structured-arrow map to compare with the comma model. -/
def toStructured : IsoFiber F b ⥤ StructuredArrow b F :=
  (isoFiberProperty F b).ι

/-- Forget the specified structure isomorphism. -/
def forget : IsoFiber F b ⥤ C := toStructured F b ⋙ StructuredArrow.proj b F

/-- An object and an actual isomorphism determine an isomorphism-fiber object. -/
def mk (X : C) (e : b ≅ F.obj X) : IsoFiber F b :=
  ⟨StructuredArrow.mk e.hom, by change IsIso e.hom; infer_instance⟩

instance (X : IsoFiber F b) : IsIso X.obj.hom := X.property

/-- A specified natural isomorphism from the constant base functor lifts an
actual functor into the isomorphism fiber. -/
def lift {A : Type*} [Category* A] (G : A ⥤ C)
    (e : (Functor.const A).obj b ≅ G ⋙ F) : A ⥤ IsoFiber F b where
  obj X := mk F b (G.obj X) (e.app X)
  map {X Y} f := ⟨StructuredArrow.homMk (G.map f) (by
    change (e.app X).hom ≫ F.map (G.map f) = (e.app Y).hom
    have h := e.hom.naturality f
    simpa using h.symm)⟩
  map_id X := by
    apply ObjectProperty.hom_ext
    apply StructuredArrow.hom_ext
    exact G.map_id X
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply StructuredArrow.hom_ext
    exact G.map_comp f g

instance lift_faithful {A : Type*} [Category* A] (G : A ⥤ C) [G.Faithful]
    (e : (Functor.const A).obj b ≅ G ⋙ F) : (lift F b G e).Faithful where
  map_injective {_ _} _ _ h := G.map_injective (congrArg (fun k ↦ k.hom.right) h)

instance lift_full {A : Type*} [Category* A] (G : A ⥤ C) [G.Full]
    (e : (Functor.const A).obj b ≅ G ⋙ F) : (lift F b G e).Full where
  map_surjective f := by
    refine ⟨G.preimage f.hom.right, ?_⟩
    apply ObjectProperty.hom_ext
    apply StructuredArrow.hom_ext
    exact G.map_preimage _

end IsoFiber
end CategoryTheory
