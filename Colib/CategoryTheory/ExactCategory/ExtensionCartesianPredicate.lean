/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.ExtensionCartesian
public import Mathlib.CategoryTheory.FiberedCategory.Cartesian

/-!
Implementation provenance:
`Quillen/CategoryTheory/ExactCategory/ExtensionCartesianPredicate.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # The standard cartesian predicate for the actual extension projection -/
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

/-- The preceding concrete factorization realizes mathlib's strongly cartesian
predicate. It does not require strict source-object lifting. -/
instance extensionProjection_stronglyCartesian {x y : E.ExtensionTotal} (f : x ⟶ y) :
    E.extensionProjection.IsStronglyCartesian (E.extensionProjection.map f) f where
  universal_property' {z} w g _ := by
    have hw : E.extensionProjectionQMap g = w ≫ E.extensionProjectionQMap f :=
      (IsHomLift.eq_of_isHomLift E.extensionProjection (w ≫ E.extensionProjection.map f) g).symm
    obtain ⟨h, hh, hu⟩ := E.existsUnique_extensionFactor f g w hw
    refine ⟨h, ⟨?_, hh.2⟩, ?_⟩
    · rw [← hh.1]
      exact IsHomLift.map E.extensionProjection h
    · intro h' hh'
      let := hh'.1
      apply hu h'
      refine ⟨?_, hh'.2⟩
      exact (IsHomLift.eq_of_isHomLift E.extensionProjection w h').symm

end CategoryTheory.ExactCategory.ExactStructure
