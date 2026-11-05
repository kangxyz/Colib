/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Mathlib.CategoryTheory.Bicategory.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses

/-!
# The category of isomorphism classes of 1-morphisms

For a bicategory `B`, `CategoryTheory.Bicategory.IsoQuotient B` has the same objects as `B` and
1-morphisms modulo invertible 2-morphisms. Whiskering makes composition
well-defined; the unitors and associator prove the category laws in the quotient.

No choice of representatives is used to define composition. The equivalence relation
is Mathlib's `CategoryTheory.isIsomorphicSetoid` on each hom-category.

## Implementation provenance

Adapted from `Quillen/Aglib/CategoryTheory/Bicategory/IsoQuotient.lean` at Quillen
commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The object wrapper, morphism
universes, quotient projection and composition on representatives are retained.
-/
@[expose] public section

universe w v u

open CategoryTheory

namespace CategoryTheory.Bicategory

/-- The objects of the category obtained by identifying isomorphic 1-morphisms
in a bicategory. The wrapper keeps its category structure separate from the
original bicategory structure. -/
structure IsoQuotient (B : Type u) where
  /-- The corresponding object of the original bicategory. -/
  obj : B

namespace IsoQuotient

variable {B : Type u} [Bicategory.{w, v} B]

/-- Two parallel 1-morphisms are equivalent precisely when there is an
invertible 2-morphism between them. -/
abbrev homSetoid (X Y : B) : Setoid (X ⟶ Y) :=
  CategoryTheory.isIsomorphicSetoid (X ⟶ Y)

/-- Composition of 1-morphisms respects isomorphism, by right and left
whiskering the given invertible 2-morphisms. -/
theorem comp_respects_iso {X Y Z : B} {f f' : X ⟶ Y} {g g' : Y ⟶ Z}
    (hf : Nonempty (f ≅ f')) (hg : Nonempty (g ≅ g')) :
    Nonempty (f ≫ g ≅ f' ≫ g') := by
  obtain ⟨ef⟩ := hf
  obtain ⟨eg⟩ := hg
  exact ⟨(Bicategory.whiskerRightIso ef g).trans (Bicategory.whiskerLeftIso f' eg)⟩

/-- The category of 1-morphisms modulo invertible 2-morphisms. -/
instance category : Category.{v} (IsoQuotient B) where
  Hom X Y := Quotient (homSetoid X.obj Y.obj)
  id X := Quotient.mk _ (𝟙 X.obj)
  comp := Quotient.map₂ (fun f g => f ≫ g)
    (fun _ _ hf _ _ hg => comp_respects_iso hf hg)
  id_comp := by
    rintro X Y ⟨f⟩
    exact Quotient.sound ⟨Bicategory.leftUnitor f⟩
  comp_id := by
    rintro X Y ⟨f⟩
    exact Quotient.sound ⟨Bicategory.rightUnitor f⟩
  assoc := by
    rintro W X Y Z ⟨f⟩ ⟨g⟩ ⟨h⟩
    exact Quotient.sound ⟨Bicategory.associator f g h⟩

/-- The morphism represented by a 1-morphism of the bicategory. -/
def mkHom {X Y : B} (f : X ⟶ Y) : mk X ⟶ mk Y :=
  Quotient.mk (homSetoid X Y) f

/-- Every quotient morphism has a representative. -/
theorem mkHom_surjective (X Y : B) :
    Function.Surjective (mkHom : (X ⟶ Y) → (mk X ⟶ mk Y)) := by
  rintro ⟨f⟩
  exact ⟨f, rfl⟩

/-- Equality in the quotient is exactly isomorphism of 1-morphisms. -/
theorem mkHom_eq_iff {X Y : B} (f g : X ⟶ Y) :
    mkHom f = mkHom g ↔ Nonempty (f ≅ g) :=
  Quotient.eq

/-- Invertible 2-morphisms become equalities of quotient morphisms. -/
theorem mkHom_eq_of_iso {X Y : B} {f g : X ⟶ Y} (e : f ≅ g) :
    mkHom f = mkHom g :=
  Quotient.sound ⟨e⟩

@[simp]
theorem mkHom_id (X : B) : mkHom (𝟙 X) = 𝟙 (mk X) := rfl

@[simp]
theorem mkHom_comp {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    mkHom (f ≫ g) = mkHom f ≫ mkHom g := rfl

end IsoQuotient

end CategoryTheory.Bicategory

attribute [colib_tag "COL-0034",
  colib_ref "WeibelKBook" "IV, Definition 6.1, equation (6.1.1)" "background"
    "Restricted-span application only; not a statement of the general bicategory quotient"]
  CategoryTheory.Bicategory.IsoQuotient
  CategoryTheory.Bicategory.IsoQuotient.category
