/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.Waldhausen.Approximation.Basic
public import Colib.CategoryTheory.Waldhausen.SplitComplexes.FactorizationSubcategory

/-!
# Approximation and saturation for split complexes

Ambient and split complex weak equivalences satisfy two-out-of-three saturation. The identity
    comparison on a cone-closed complex subcategory has the two approximation properties.
-/
/-! Adapted from `Quillen.Waldhausen.SplitComplexes.Approximation`
at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CochainComplex

universe v u v' u'

namespace CategoryTheory.Waldhausen

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The saturation axiom for actual quasi-isomorphisms in the ambient model. -/
theorem complexes_saturated : (complexes A).weq.HasTwoOutOfThreeProperty :=
  inferInstanceAs ((HomologicalComplex.quasiIso A (ComplexShape.up ℤ)).HasTwoOutOfThreeProperty)

/-- Changing the cofibrations to split maps retains saturation. -/
theorem splitComplexes_saturated : (splitComplexes A).weq.HasTwoOutOfThreeProperty :=
  complexes_saturated

attribute [local instance] Abelian.hasFiniteBiproducts

variable (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]

/-- Saturation is inherited by the actual full complex subcategory. -/
theorem complexSubcategory_saturated : (complexSubcategory P).weq.HasTwoOutOfThreeProperty :=
  inferInstanceAs (((HomologicalComplex.quasiIso A (ComplexShape.up ℤ)).inverseImage
    P.ι).HasTwoOutOfThreeProperty)

/-- Saturation also holds with the split-cofibration convention. -/
theorem splitComplexSubcategory_saturated :
    (splitComplexSubcategory P).weq.HasTwoOutOfThreeProperty :=
  complexSubcategory_saturated P

/-- Both approximation properties are proved for the canonical identity
comparison, provided the actual object predicate is closed under cones. -/
theorem splitComparison_approximation
    (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L →
      ∀ f : K ⟶ L, P (mappingCone f)) :
    HasApproximationProperty (splitComplexSubcategory P) (complexSubcategory P)
      (𝟭 P.FullSubcategory) where
  reflects _ h := h
  lift f := SplitFactorization.exists_subcategory_factorization P hcone f

end CategoryTheory.Waldhausen

end
