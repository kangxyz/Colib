/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Extensions.Basic

/-!
Implementation provenance:
`Quillen/Aglib/CategoryTheory/ExactCategory/Extensions/Pullback.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Pullback of admissible extensions

Any base morphism pulls back admissible epimorphisms and their cores.
Only exact-category pullbacks of deflations are used; arbitrary ambient
finite limits are not assumed.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C)

local instance extensionHasPullback {X Y : C} (f : X ⟶ Y) (p : E.ExtensionOver Y) :
    HasPullback p.obj.hom f := E.deflation.hasPullback f p.property

/-- Pull back admissible epimorphisms along any map, using exactly the existing
exact-category pullback axiom. -/
def extensionPullback {X Y : C} (f : X ⟶ Y) : E.ExtensionOver Y ⥤ E.ExtensionOver X where
  obj p := ⟨Over.mk (pullback.snd p.obj.hom f),
    E.deflation.pullback_snd _ _ p.property⟩
  map {p q} g := ObjectProperty.homMk (Over.homMk
    (pullback.lift (pullback.fst _ _ ≫ g.hom.left) (pullback.snd _ _)
      (by rw [Category.assoc, Over.w, pullback.condition])) (by simp))
  map_id p := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;> simp
  map_comp g h := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;> simp [Category.assoc]

/-- Pullback on the isomorphism groupoids of extensions. -/
def extensionFiberPullback {X Y : C} (f : X ⟶ Y) :
    E.ExtensionFiber Y ⥤ E.ExtensionFiber X := (E.extensionPullback f).core

end CategoryTheory.ExactCategory.ExactStructure
