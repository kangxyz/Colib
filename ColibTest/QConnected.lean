/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.CategoryTheory.QConstruction.ZeroEndomorphisms

/-!
# The distinguished Q-vertex and connectedness regression tests

These tests use an arbitrary exact structure and independent object and hom
universes. They distinguish existence of the chosen arrows from zero from
uniqueness of arrows to an original zero object. They assert neither initiality
nor terminality nor a zero-object structure on the distinguished Q-vertex.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped ZeroObject

universe v u

noncomputable section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

example : Category E.QCategory := inferInstance

example : E.qZero = QConstruction.of E.deflation E.inflation (0 : C) := rfl

example (X : E.QCategory) : E.qZero ⟶ X := E.fromZero X

example (X : C) :
    E.fromZero (QConstruction.of E.deflation E.inflation X) =
      QConstruction.mkHom E.deflation E.inflation
        { apex := (0 : C)
          l := 𝟙 _
          r := 0
          wl := E.deflation_id _
          wr := E.inflation_zero X } := rfl

example : Nonempty E.QCategory := inferInstance

example : IsConnected E.QCategory := inferInstance

example {α : Type*} (f : E.QCategory → α)
    (hf : ∀ {X Y : E.QCategory}, (X ⟶ Y) → f X = f Y) (X Y : E.QCategory) :
    f X = f Y := (hf (E.fromZero X)).symm.trans (hf (E.fromZero Y))

example (f : E.qZero ⟶ E.qZero) : f = 𝟙 E.qZero := E.qZero_endomorphism_eq_id f

example : E.fromZero E.qZero = 𝟙 E.qZero := E.qZero_endomorphism_eq_id _

example : Subsingleton (E.qZero ⟶ E.qZero) := inferInstance

example (e e' : E.qZero ≅ E.qZero) : e = e' := Subsingleton.elim _ _

example (X Y : E.QCategory) (hY : IsZero Y.obj.of) : Subsingleton (X ⟶ Y) :=
  E.qHom_subsingleton_of_isZero X Y hY

example (X : E.QCategory) (f g : X ⟶ E.qZero) : f = g :=
  (E.qHom_subsingleton_of_isZero X E.qZero (isZero_zero C)).elim f g
