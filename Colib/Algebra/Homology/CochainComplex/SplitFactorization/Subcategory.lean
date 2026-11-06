/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Subcategory

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.FactorizationQuotient

/-!
# Membership of the actual factorization middle object

In an extension-closed cone-closed property of cochain complexes, the original
identity-cone biproduct middle object stays in the property. All original
closure hypotheses and the actual factorization object are retained.
-/
/-! Adapted from `Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.Subcategory`
at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CochainComplex

universe v u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace CochainComplex.SplitFactorization

variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L →
    ∀ f : K ⟶ L, P (mappingCone f))

include hcone

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderFiniteProducts] in
/-- The explicit factorization object stays in a cone-closed subcategory. -/
theorem middle_property {K L : CochainComplex A ℤ} (hK : P K) (hL : P L) (f : K ⟶ L) :
    P (middle f) :=
  (abelianExactStructure (CochainComplex A ℤ)).prop_biprod P (hcone hK hK (𝟙 K)) hL

end CochainComplex.SplitFactorization
