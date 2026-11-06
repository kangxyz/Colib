module

public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.ComplexSecondEndpoint

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration CochainComplex
universe u v

variable {A : Type u} [Category.{v} A] [Abelian A]

example {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    SplitFactorization.middle f = (mappingCone (𝟙 K) ⊞ L) := rfl

example {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    SplitFactorization.inclusion f = biprod.lift (mappingCone.inr (𝟙 K)) f := rfl

example {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    SplitFactorization.inclusion f ≫ SplitFactorization.projection f = f :=
  SplitFactorization.inclusion_projection f

example {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    biprod.inr ≫ SplitFactorization.jointInclusion f ≫
      SplitFactorization.projection f = 𝟙 L := by
  rw [← Category.assoc, SplitFactorization.jointInclusion, biprod.inr_desc]
  exact biprod.inr_snd

attribute [local instance] Abelian.hasFiniteBiproducts

variable (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L → ∀ f : K ⟶ L, P (mappingCone f))
  (hshift : ∀ K, P K → P (K⟦(1 : ℤ)⟧))

example : RowFactorization.SecondEndpointSection (complexSubcategoryNested P)
    (complexJointData P hcone hshift) :=
  complexJointData_secondEndpointSection P hcone hshift

example (n : SimplexCategory) :
    let W := QuotientRows.waldhausenStructure
      (ofExactCategory (ExactSubcategory.exactStructure
        (abelianExactStructure (CochainComplex A ℤ)) P)) n
    IsExact (ArrowCategory.waldhausenStructure W).cof (ArrowCategory.waldhausenStructure W).weq
      W.cof W.weq (complexRowFactorization P hcone hshift n).middle :=
  complexRowFactorization_middle_exact P hcone hshift n
