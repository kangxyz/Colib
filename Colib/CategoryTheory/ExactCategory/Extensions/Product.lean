/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.Extensions.Pullback
public import Mathlib.CategoryTheory.Products.Basic

/-!
Implementation provenance:
`Quillen/Aglib/CategoryTheory/ExactCategory/Extensions/Product.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Pullback multiplication of extensions with fixed quotient

The middle object of the product is the actual pullback over the fixed quotient.
Its deflation is obtained by composition of admissible deflations, using only
the exact-category pullback axiom.
-/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C)

/-- The unit extension has identity quotient map. -/
def extensionUnit (X : C) : E.ExtensionFiber X :=
  ⟨⟨Over.mk (𝟙 X), E.deflation_id X⟩⟩

/-- Admissibility supplies the pullback used in multiplication. -/
instance extensionProductHasPullback {X : C} (p q : E.ExtensionOver X) :
    HasPullback p.obj.hom q.obj.hom := E.deflation.hasPullback q.obj.hom p.property

/-- The actual pullback product of two extensions over a fixed object. -/
def extensionProductObj {X : C} (p q : E.ExtensionOver X) : E.ExtensionOver X :=
  ⟨Over.mk (pullback.snd p.obj.hom q.obj.hom ≫ q.obj.hom),
    E.deflation_comp _ _ (E.deflation.pullback_snd _ _ p.property) q.property⟩

/-- Pullback multiplication is functorial in both extension maps. -/
def extensionProduct (X : C) : E.ExtensionOver X × E.ExtensionOver X ⥤ E.ExtensionOver X where
  obj p := E.extensionProductObj p.1 p.2
  map {p q} f := ObjectProperty.homMk (Over.homMk
    (pullback.map p.1.obj.hom p.2.obj.hom q.1.obj.hom q.2.obj.hom
      f.1.hom.left f.2.hom.left (𝟙 X) (by simp [Over.w]) (by simp [Over.w]))
    (by simp [extensionProductObj, Category.assoc, Over.w]))
  map_id p := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact pullback.map_id
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;> simp [Category.assoc]

/-- Multiplication on the actual isomorphism groupoids of extensions. -/
def extensionFiberProduct (X : C) :
    E.ExtensionFiber X × E.ExtensionFiber X ⥤ E.ExtensionFiber X where
  obj p := ⟨E.extensionProductObj p.1.of p.2.of⟩
  map f := ⟨(E.extensionProduct X).mapIso (Iso.prod f.1.iso f.2.iso)⟩
  map_id p := by
    apply Core.hom_ext
    exact (E.extensionProduct X).map_id (p.1.of, p.2.of)
  map_comp f g := by
    apply Core.hom_ext
    exact (E.extensionProduct X).map_comp (Prod.mkHom f.1.iso.hom f.2.iso.hom)
      (Prod.mkHom g.1.iso.hom g.2.iso.hom)

/-- The diagonal is a genuine map of extensions into their pullback square. -/
def extensionDiagonal {X : C} (p : E.ExtensionOver X) : p ⟶ E.extensionProductObj p p :=
  ObjectProperty.homMk (Over.homMk (pullback.lift (𝟙 _) (𝟙 _) (by simp))
    (by simp [extensionProductObj]))

/-- Naturality of the actual middle-term diagonal. -/
theorem extensionDiagonal_naturality {X : C} {p q : E.ExtensionOver X} (f : p ⟶ q) :
    f ≫ E.extensionDiagonal q =
      E.extensionDiagonal p ≫ (E.extensionProduct X).map (Prod.mkHom f f) := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext <;> simp [extensionDiagonal, extensionProduct]

end CategoryTheory.ExactCategory.ExactStructure
