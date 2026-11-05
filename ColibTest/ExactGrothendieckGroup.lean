/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.GrothendieckGroup.FieldExact

/-!
# Exact-category Grothendieck group regression tests

These tests retain arbitrary exact structures before specializing to the standard
abelian structure and finite-dimensional vector spaces. They concern algebraic K₀,
not a homotopy group of the Q-construction.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory

universe v u w

section ExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

example (S : ShortComplex C) (hS : E.conflation S) :
    E.grothendieckClass S.X₂ - E.grothendieckClass S.X₁ =
      E.grothendieckClass S.X₃ := by
  rw [E.grothendieckClass_additive hS, add_sub_cancel_left]

example {X Y : C} (e : X ≅ Y) : E.grothendieckClass X = E.grothendieckClass Y :=
  E.grothendieckClass_iso e

example (X : C) (hX : IsZero X) : E.grothendieckClass X = 0 :=
  E.grothendieckClass_of_isZero hX

example {A : Type w} [AddCommGroup A] (f : C → A) (hf : E.IsAdditiveInvariant f) :
    ∃! g : E.GrothendieckGroup →+ A, ∀ X, g (E.grothendieckClass X) = f X :=
  E.grothendieck_universal f hf

example {A : Type w} [AddCommGroup A] (f : C → A) (hf : E.IsAdditiveInvariant f)
    (X : C) : E.grothendieckLift f hf (E.grothendieckClass X) = f X := by
  simp

end ExactStructure

section Abelian

variable (C : Type u) [Category.{v} C] [Abelian C]

attribute [local instance] Abelian.hasFiniteBiproducts

example (X : C) :
    abelianGrothendieckEquiv C ((abelianExactStructure C).grothendieckClass X) =
      GrothendieckGroup.of X := by
  simp

example (X : C) :
    (abelianGrothendieckEquiv C).symm (GrothendieckGroup.of X) =
      (abelianExactStructure C).grothendieckClass X := by
  simp

example (S : ShortComplex C) (hS : S.ShortExact) :
    abelianGrothendieckEquiv C ((abelianExactStructure C).grothendieckClass S.X₂) =
      GrothendieckGroup.of S.X₁ + GrothendieckGroup.of S.X₃ := by
  simpa using GrothendieckGroup.additivity hS

end Abelian

section Field

variable (k : Type u) [Field k]

attribute [local instance] Abelian.hasFiniteBiproducts

example (V : FGModuleCat.{u} k) :
    fgModuleExactRankEquiv k
      ((abelianExactStructure (FGModuleCat.{u} k)).grothendieckClass V) =
        (Module.finrank k V : ℤ) := by
  simp

example :
    fgModuleExactRankEquiv k
      ((abelianExactStructure (FGModuleCat.{u} k)).grothendieckClass (FGModuleCat.of k k)) =
        1 := by
  simp

example (n : ℤ) :
    fgModuleExactRankEquiv k
      (n • (abelianExactStructure (FGModuleCat.{u} k)).grothendieckClass
        (FGModuleCat.of k k)) = n := by
  simp

example (V : FGModuleCat.{u} k) :
    (fgModuleExactRankEquiv k).symm (Module.finrank k V : ℤ) =
      (abelianExactStructure (FGModuleCat.{u} k)).grothendieckClass V := by
  apply (fgModuleExactRankEquiv k).injective
  simp

end Field
