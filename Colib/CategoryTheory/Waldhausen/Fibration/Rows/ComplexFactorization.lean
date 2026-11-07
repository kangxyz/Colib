/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.JointFactorization
public import Colib.CategoryTheory.Waldhausen.Fibration.ComplexChainReplacement
public import Colib.CategoryTheory.Waldhausen.Cylinder.JointExact

/-! # The actual identity-cone factorization on fine quotient rows

The accepted complex joint cylinder supplies every structural input to the
row lift. The middle, first factor and projection remain the original
identity-cone formulas at each interval. Reedy row cofibrancy and exact
middle functoriality are proved, rather than inferred from component cofibrancy.
-/
/-! Adapted from `Quillen.Waldhausen.Fibration.Rows.ComplexFactorization`
at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CategoryTheory.Waldhausen.SplitFactorization


open CategoryTheory.ExactCategory

noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration
open CategoryTheory.Waldhausen.SplitFactorization CochainComplex.SplitFactorization
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L →
    ∀ f : K ⟶ L, P (mappingCone f))
  (hshift : ∀ K, P K → P (K⟦(1 : ℤ)⟧))

/-- The genuine complex cylinder satisfies all base joint data, with literal maps. -/
@[colib_tag "COL-0258",
  colib_ref "quillen" "Quillen/Waldhausen/Fibration/Rows/ComplexFactorization.lean:46-60"
    "adaptation" "Actual identity-cone joint cylinder from cone and shift closure"]
def complexJointData : RowFactorization.JointData (complexSubcategoryNested P) where
  joint := subcategoryJointFunctor P hcone hshift
  exact := subcategoryJointFunctor_isoExact P hcone hshift
  inl := subcategoryJointSourceInl P
  inr := subcategoryJointSourceInr P
  coproduct := subcategoryJointSourceCofanIsColimit P
  projection := (complexSubcategoryFactorization P hcone).projection
  factorization f := by
    apply ObjectProperty.hom_ext
    change biprod.inl ≫ jointInclusion f.hom.hom ≫ CochainComplex.SplitFactorization.projection
      f.hom.hom = _
    rw [← Category.assoc, jointInclusion, biprod.inl_desc]
    exact inclusion_projection f.hom.hom
  weak := (complexSubcategoryFactorization P hcone).weak

/-- The actual fine quotient-row cylinder factorization, with coarse quasi-isomorphism
projection. -/
def complexRowFactorization (n : SimplexCategory) :
    FunctorialFactorization (RowWeakEquivalences.coarseStructure (complexSubcategoryNested P) n) :=
  RowFactorization.factorization (complexSubcategoryNested P) (complexJointData P hcone hshift) n

/-- The original middle functor on rows is genuinely exact for fine weak equivalences. -/
theorem complexRowFactorization_middle_exact (n : SimplexCategory) :
    let W := QuotientRows.waldhausenStructure
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex A
        ℤ)) P)) n
    IsExact (ArrowCategory.waldhausenStructure W).cof (ArrowCategory.waldhausenStructure W).weq
      W.cof W.weq (complexRowFactorization P hcone hshift n).middle :=
  RowFactorization.middle_exact (complexSubcategoryNested P) (complexJointData P hcone hshift) n

/-- The unchanged inclusion satisfies the genuine original Reedy row cofibration tests. -/
theorem complexRowFactorization_cof {n : SimplexCategory}
    (f : Arrow (QuotientRows.Obj
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex A
        ℤ)) P)) n)) :
    QuotientRows.cof _ n ((complexRowFactorization P hcone hshift n).inclusion.app f) :=
  (complexRowFactorization P hcone hshift n).cofibration f

/-- Its exact original component is the original identity-cone first factor. -/
@[simp] theorem complexRowFactorization_inclusion_component {n : SimplexCategory}
    (f : Arrow (QuotientRows.Obj
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex A
        ℤ)) P)) n))
    (p : Interval n) :
    (((complexRowFactorization P hcone hshift n).inclusion.app f).hom.app p).hom =
      CochainComplex.SplitFactorization.inclusion (f.hom.hom.app p).hom := by
  change biprod.inl ≫ jointInclusion (f.hom.hom.app p).hom = _
  exact biprod.inl_desc _ _

/-- Its exact original component is the original identity-cone projection. -/
@[simp] theorem complexRowFactorization_projection_component {n : SimplexCategory}
    (f : Arrow (QuotientRows.Obj
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex A
        ℤ)) P)) n))
    (p : Interval n) :
    (((complexRowFactorization P hcone hshift n).projection.app f).hom.app p).hom =
      CochainComplex.SplitFactorization.projection (f.hom.hom.app p).hom := rfl

/-- Every original projection component is an actual quasi-isomorphism. -/
theorem complexRowFactorization_projection_quasi {n : SimplexCategory}
    (f : Arrow (QuotientRows.Obj
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex A
        ℤ)) P)) n))
    (p : Interval n) :
    QuasiIso (((complexRowFactorization P hcone hshift n).projection.app f).hom.app p).hom :=
  (complexRowFactorization P hcone hshift n).weak f p

/-- Fine square preservation is genuine and ready for the original mixed finite-chain
replacement. -/
theorem complexRowFactorization_fineSquares (n : SimplexCategory) :
    MixedChainReplacement.PreservesFineSquares (RowWeakEquivalences.nested
      (complexSubcategoryNested P) n)
      (complexRowFactorization P hcone hshift n) :=
  RowFactorization.factorization_fineSquares (complexSubcategoryNested P) (complexJointData P
    hcone hshift) n

end CategoryTheory.Waldhausen.Fibration
