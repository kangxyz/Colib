/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.SecondEndpoint
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.ComplexFactorization


/-! # The actual identity-cone second endpoint on complex quotient rows

Adapted from the complex specialization in
`Quillen/Waldhausen/Fibration/Rows/SecondEndpoint.lean:97-144`
at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd.

The second endpoint is a genuine row cofibration by the original endpoint
coproduct pushout. Its projection-section identity is a separate structural
datum, absent from JointData; the actual identity-cone cylinder proves it
literally. Coarse two-out-of-three then makes both endpoints coarse-weak
whenever the original arrow is coarse-weak.
-/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration

attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L → ∀ f : K ⟶ L, P (mappingCone f))
  (hshift : ∀ K, P K → P (K⟦(1 : ℤ)⟧))

/-- The actual identity-cone joint cylinder proves the second-endpoint section identity. -/
@[colib_tag "COL-0258",
  colib_ref "quillen" "Quillen/Waldhausen/Fibration/Rows/SecondEndpoint.lean:106-115"
    "adaptation" "Original target biproduct endpoint is a section of the original projection"]
theorem complexJointData_secondEndpointSection :
    RowFactorization.SecondEndpointSection (complexSubcategoryNested P) (complexJointData P
      hcone hshift) := by
  intro f
  apply ObjectProperty.hom_ext
  change biprod.inr ≫ CochainComplex.SplitFactorization.jointInclusion f.hom.hom ≫
    CochainComplex.SplitFactorization.projection f.hom.hom = 𝟙 _
  rw [← Category.assoc, CochainComplex.SplitFactorization.jointInclusion, biprod.inr_desc]
  exact biprod.inr_snd

/-- The actual complex row target endpoint, retaining the original ambient biproduct inclusion. -/
def complexRowTargetInclusion (n : SimplexCategory) :
    Arrow.rightFunc ⟶ (complexRowFactorization P hcone hshift n).middle :=
  RowFactorization.targetInclusion (complexSubcategoryNested P) (complexJointData P hcone hshift) n

/-- Its unchanged component is literally the original target biproduct inclusion. -/
@[simp] theorem complexRowTargetInclusion_component {n : SimplexCategory}
    (f : Arrow (QuotientRows.Obj
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex A
        ℤ)) P)) n))
    (p : Interval n) :
    (((complexRowTargetInclusion P hcone hshift n).app f).hom.app p).hom =
      (biprod.inr : (f.right.obj.obj p).obj ⟶ CochainComplex.SplitFactorization.middle
        (f.hom.hom.app p).hom) := by
  change biprod.inr ≫ CochainComplex.SplitFactorization.jointInclusion (f.hom.hom.app p).hom = _
  exact biprod.inr_desc _ _

/-- The original complex row projection retracts this actual target inclusion exactly. -/
@[reassoc] theorem complexRowTargetInclusion_projection {n : SimplexCategory}
    (f : Arrow (QuotientRows.Obj
      (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex A
        ℤ)) P)) n)) :
    (complexRowTargetInclusion P hcone hshift n).app f ≫
      (complexRowFactorization P hcone hshift n).projection.app f = 𝟙 f.right :=
  RowFactorization.targetInclusion_projection (complexSubcategoryNested P) (complexJointData P
    hcone hshift)
    (complexJointData_secondEndpointSection P hcone hshift) f

end CategoryTheory.Waldhausen.Fibration
