/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.QConstruction.Abelian.Surjections

/-! # Ordinary monomorphisms embed in the abelian Q-construction

Extracted from AuxiliaryRefinement at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd.
The proof uses native span representatives and independent object and hom universes.
-/

@[expose] public noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
namespace CategoryTheory.QConstruction
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Ordinary monomorphisms retain their underlying map in the Q-construction. -/
theorem inflationArrow_injective {X Y : C} (f g : X ⟶ Y) [Mono f] [Mono g]
    (h : inflationArrow f = inflationArrow g) : f = g := by
  obtain ⟨e, hl, hr⟩ := (mkHom_eq_iff_apexIso _ _ _ _).1 h
  change e.hom ≫ 𝟙 X = 𝟙 X at hl
  change e.hom ≫ g = f at hr
  have he : e.hom = 𝟙 X := by simpa using hl
  simpa [he] using hr.symm

end CategoryTheory.QConstruction
