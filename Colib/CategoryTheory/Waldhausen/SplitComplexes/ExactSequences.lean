/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.ExactSequences
public import Colib.Algebra.Homology.CochainComplex.DegreewiseSplitMono
public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.Waldhausen.SplitComplexes.Subcategory

/-!
# Split cofibrations and degreewise split exact sequences

This identifies the cofibrations of the split full-subcategory model with
actual degreewise split short exact sequences whose quotient lies in the
subcategory. The degreewise retractions are extended to full short-complex
splittings using exactness; no chain splitting is required.
-/
/-! Adapted from `Quillen.Waldhausen.SplitComplexes.ExactSequences`
at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CochainComplex


open CategoryTheory.ExactCategory


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe v u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace CategoryTheory.Waldhausen

variable {A : Type u} [Category.{v} A] [Abelian A]

variable (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]

/-- The cofibrations are precisely first arrows of actual degreewise split
short exact sequences with quotient in the full subcategory. -/
theorem splitSubcategoryCofibrations_iff {K L : P.FullSubcategory} (i : K ⟶ L) :
    splitSubcategoryCofibrations P i ↔
      ∃ (Z : CochainComplex A ℤ) (_hZ : P Z) (p : L.obj ⟶ Z) (hp : i.hom ≫ p = 0),
        ∀ n : ℤ, Nonempty
          ((ShortComplex.mk i.hom p hp).map (eval A (ComplexShape.up ℤ) n)).Splitting := by
  constructor
  · intro hi
    obtain ⟨Z, hZ, p, hp, hS⟩ :=
      (ExactSubcategory.inflation_iff (abelianExactStructure _) P i).1 hi.1
    exact ⟨Z, hZ, p, hp, fun n ↦ ⟨degreewiseSplittingOfShortExact hS hi.2 n⟩⟩
  · rintro ⟨Z, hZ, p, hp, h⟩
    obtain ⟨hS, hi⟩ := shortExact_and_degreewiseSplitMono_of_splittings h
    exact ⟨(ExactSubcategory.inflation_iff (abelianExactStructure _) P i).2
      ⟨Z, hZ, p, hp, hS⟩, hi⟩

end CategoryTheory.Waldhausen
