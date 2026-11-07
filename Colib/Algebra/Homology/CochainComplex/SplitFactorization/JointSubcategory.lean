/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.ComplexQuotient
public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.SubcategoryFunctor
public import Colib.CategoryTheory.ExactCategory.Subcategory

/-!
# The actual two endpoints and their inherited inclusion

The original biproduct endpoint object and joint inclusion lift to the
cone-closed full complex subcategory with their stated closure hypotheses.
-/
/-! Adapted from `Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.JointSubcategory`
at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CochainComplex
universe v u

namespace CochainComplex.SplitFactorization

attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L →
    ∀ f : K ⟶ L, P (mappingCone f))
  (hshift : ∀ K, P K → P (K⟦(1 : ℤ)⟧))

/-- The two actual endpoints as an inherited object. -/
def subcategoryJointSource (f : Arrow P.FullSubcategory) : P.FullSubcategory :=
  ⟨f.left.obj ⊞ f.right.obj,
    (abelianExactStructure (CochainComplex A ℤ)).prop_biprod P f.left.property f.right.property⟩

/-- Both original endpoints into the original factorization object. -/
def subcategoryJointInclusion (f : Arrow P.FullSubcategory) :
    subcategoryJointSource P f ⟶ (subcategoryMiddleFunctor P hcone).obj f :=
  P.homMk (jointInclusion f.hom.hom)

end CochainComplex.SplitFactorization
