/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.JointSubcategory
public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.ComplexQuotient
public import Colib.CategoryTheory.Waldhausen.SplitComplexes.FunctorialFactorization
public import Colib.CategoryTheory.ExactCategory.SubcategoryCokernel

/-! # Joint and relative cylinder cofibrations in actual complex subcategories

The displayed relative quotient is the shifted actual cokernel of the source
map. Its membership follows from inherited admissibility and shift closure;
closure under arbitrary quotients is neither required nor asserted.
-/
/-! Adapted from `Quillen.Waldhausen.Cylinder.Subcategory`
at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CochainComplex
universe v u

open CochainComplex.SplitFactorization

namespace CategoryTheory.Waldhausen.SplitFactorization

attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L →
    ∀ f : K ⟶ L, P (mappingCone f))
  (hshift : ∀ K, P K → P (K⟦(1 : ℤ)⟧))

include hshift in
/-- Joint endpoints form an actual inherited split cofibration. -/
theorem subcategoryJointInclusion_cof (f : Arrow P.FullSubcategory) :
    (splitComplexSubcategory P).cof (subcategoryJointInclusion P hcone f) := by
  refine ⟨?_, jointInclusion_degreewiseSplitMono f.hom.hom⟩
  apply (ExactSubcategory.inflation_iff (abelianExactStructure (CochainComplex A ℤ)) P
    (subcategoryJointInclusion P hcone f)).2
  exact ⟨f.left.obj⟦(1 : ℤ)⟧, hshift _ f.left.property,
    jointProjection f.hom.hom, jointInclusion_projection f.hom.hom,
    jointSequence_shortExact f.hom.hom⟩

variable {f g : Arrow P.FullSubcategory} (α : f ⟶ g)
  {R : P.FullSubcategory}
  (i : (subcategoryMiddleFunctor P hcone).obj f ⟶ R)
  (j : subcategoryJointSource P g ⟶ R)
  (h : IsPushout (jointInclusion f.hom.hom) (biprod.map α.left.hom α.right.hom) i.hom j.hom)
  (k : R ⟶ (subcategoryMiddleFunctor P hcone).obj g)
  (hi : i ≫ k = (subcategoryMiddleFunctor P hcone).map α)
  (hj : j ≫ k = subcategoryJointInclusion P hcone g)

include h hi hj hshift in
/-- The actual relative joint-endpoint map is an inherited split cofibration.
Only the source map of the square needs to be a split cofibration. -/
theorem subcategoryRelativeJoint_cof
    (hα : (splitComplexSubcategory P).cof α.left) :
    (splitComplexSubcategory P).cof k := by
  let β := P.ι.mapArrow.map α
  have hi' : i.hom ≫ k.hom = middleFunctor.map β :=
    congrArg (fun z ↦ z.hom) hi
  have hj' : j.hom ≫ k.hom = jointInclusion g.hom.hom :=
    congrArg (fun z ↦ z.hom) hj
  have hQ : P (cokernel α.left.hom) :=
    ExactSubcategory.cokernel_mem_of_inflation _ P α.left hα.1
  refine ⟨?_, relative_jointInclusion_degreewiseSplitMono β hα.2 h k.hom hi' hj'⟩
  apply (ExactSubcategory.inflation_iff (abelianExactStructure (CochainComplex A ℤ)) P k).2
  exact ⟨(cokernel α.left.hom)⟦(1 : ℤ)⟧, hshift _ hQ,
    relativeQuotientProjection β, relativeQuotient_zero β h k.hom hi' hj',
    relativeQuotientSequence_shortExact β h k.hom hi' hj' hα.2⟩

end CategoryTheory.Waldhausen.SplitFactorization
