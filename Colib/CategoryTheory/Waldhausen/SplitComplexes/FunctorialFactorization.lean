/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.SubcategoryFunctor
public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.Waldhausen.FunctorialFactorization.Basic
public import Colib.CategoryTheory.Waldhausen.SplitComplexes.Approximation
public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.FactorizationFunctor

/-!
# Functorial factorizations in split-complex models

The identity-cone middle-object functor gives functorial split-cofibration factorizations on
    complexes and on the stated cone-closed full subcategories.
-/
/-! Adapted from `Quillen.Waldhausen.SplitComplexes.FunctorialFactorization`
at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CochainComplex

universe v u

namespace CategoryTheory.Waldhausen

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The actual functorial factorization on all complexes with split cofibrations. -/
def splitComplexesFunctorialFactorization : FunctorialFactorization (splitComplexes A) where
  middle := CochainComplex.SplitFactorization.middleFunctor
  inclusion := CochainComplex.SplitFactorization.inclusionNat
  projection := CochainComplex.SplitFactorization.projectionNat
  factorization f := CochainComplex.SplitFactorization.inclusion_projection f.hom
  cofibration f := CochainComplex.SplitFactorization.inclusion_degreewiseSplitMono f.hom
  weak f := CochainComplex.SplitFactorization.projection_quasiIso f.hom

attribute [local instance] Abelian.hasFiniteBiproducts

variable (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L →
    ∀ f : K ⟶ L, P (mappingCone f))

/-- The actual functorial factorization stays in the cone-closed full subcategory. -/
def splitSubcategoryFunctorialFactorization : FunctorialFactorization (splitComplexSubcategory
    P) where
  middle := subcategoryMiddleFunctor P hcone
  inclusion := {
    app f := P.homMk (CochainComplex.SplitFactorization.inclusion f.hom.hom)
    naturality _ _ α := ObjectProperty.hom_ext _
      (CochainComplex.SplitFactorization.inclusion_naturality (P.ι.mapArrow.map α)).symm }
  projection := {
    app f := P.homMk (CochainComplex.SplitFactorization.projection f.hom.hom)
    naturality _ _ α := ObjectProperty.hom_ext _
      (CochainComplex.SplitFactorization.projection_naturality (P.ι.mapArrow.map α)) }
  factorization f := ObjectProperty.hom_ext _
    (CochainComplex.SplitFactorization.inclusion_projection f.hom.hom)
  cofibration f := by
    apply (splitSubcategoryCofibrations_iff P _).2
    exact ⟨mappingCone (-f.hom.hom), hcone f.left.property f.right.property (-f.hom.hom),
      CochainComplex.SplitFactorization.quotientMap f.hom.hom,
      CochainComplex.SplitFactorization.inclusion_quotientMap f.hom.hom,
      fun n ↦ ⟨CochainComplex.SplitFactorization.quotientSequenceSplitting f.hom.hom n⟩⟩
  weak f := CochainComplex.SplitFactorization.projection_quasiIso f.hom.hom

end CategoryTheory.Waldhausen

end
