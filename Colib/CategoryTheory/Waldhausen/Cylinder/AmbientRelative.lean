/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.AmbientRelative
public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.Waldhausen.Cylinder.Subcategory
public import Colib.CategoryTheory.Waldhausen.SplitComplexes.FunctorialFactorization

/-! # Relative cylinder cofibrations for ambient admissible monomorphisms

The relative map is admissible without a degreewise splitting assumption.
Its genuine quotient is the shifted actual source cokernel. This addresses
the ambient-cofibration model separately from its split-cofibration variant.
-/
/-! Adapted from `Quillen.Waldhausen.Cylinder.AmbientRelative`
at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
universe u v

open CochainComplex.SplitFactorization

namespace CategoryTheory.Waldhausen.SplitFactorization
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  {f g : Arrow (CochainComplex A ℤ)} (α : f ⟶ g)
  {R : CochainComplex A ℤ} {i : middle f.hom ⟶ R} {j : g.left ⊞ g.right ⟶ R}
  (h : IsPushout (jointInclusion f.hom) (biprod.map α.left α.right) i j)
  (k : R ⟶ middle g.hom) (hi : i ≫ k = middleFunctor.map α)
  (hj : j ≫ k = jointInclusion g.hom)

variable (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L →
    ∀ f : K ⟶ L, P (mappingCone f))
  (hshift : ∀ K, P K → P (K⟦(1 : ℤ)⟧))
  {f' g' : Arrow P.FullSubcategory} (β : f' ⟶ g') {T : P.FullSubcategory}
  (i' : (subcategoryMiddleFunctor P hcone).obj f' ⟶ T)
  (j' : subcategoryJointSource P g' ⟶ T)
  (h' : IsPushout (jointInclusion f'.hom.hom) (biprod.map β.left.hom β.right.hom) i'.hom j'.hom)
  (k' : T ⟶ (subcategoryMiddleFunctor P hcone).obj g')
  (hi' : i' ≫ k' = (subcategoryMiddleFunctor P hcone).map β)
  (hj' : j' ≫ k' = subcategoryJointInclusion P hcone g')

include hshift h' hi' hj' in
/-- Ordinary inherited admissibility of the source map proves the ordinary
inherited relative-cylinder cofibration, including actual quotient membership. -/
theorem subcategoryRelativeJoint_ambient_cof
    (hβ : (complexSubcategory P).cof β.left) : (complexSubcategory P).cof k' := by
  let γ := P.ι.mapArrow.map β
  let : Mono β.left.hom := (abelianExactStructure_inflation_iff _ _).1
    ((ExactSubcategory.exactInclusion (abelianExactStructure (CochainComplex A ℤ)) P).map_inflation
      β.left hβ)
  let : Mono γ.left := inferInstanceAs (Mono β.left.hom)
  have h₁ : i'.hom ≫ k'.hom = middleFunctor.map γ := congrArg (fun z ↦ z.hom) hi'
  have h₂ : j'.hom ≫ k'.hom = jointInclusion g'.hom.hom := congrArg (fun z ↦ z.hom) hj'
  have hQ : P (cokernel β.left.hom) :=
    ExactSubcategory.cokernel_mem_of_inflation _ P β.left hβ
  apply (ExactSubcategory.inflation_iff (abelianExactStructure (CochainComplex A ℤ)) P k').2
  exact ⟨(cokernel β.left.hom)⟦(1 : ℤ)⟧, hshift _ hQ,
    relativeQuotientProjection γ, relativeQuotient_zero γ h' k'.hom h₁ h₂,
    relativeQuotientSequence_shortExact_of_mono γ h' k'.hom h₁ h₂⟩

end CategoryTheory.Waldhausen.SplitFactorization
