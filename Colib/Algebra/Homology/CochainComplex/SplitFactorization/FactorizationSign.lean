/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.FactorizationQuotient
public import Colib.Algebra.Homology.MappingCone.Sign

/-!
# The signed quotient of the original split factorization

The original quotient is Cone(−f). Its explicit sign isomorphism gives a displayed short exact
sequence ending in Cone(f), preserving the original middle object and first map.
-/
/-! Adapted from
`Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.FactorizationSign`
at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits CochainComplex
universe u v
namespace CochainComplex.SplitFactorization
variable {A : Type u} [Category.{v} A] [Abelian A]
  {K L : CochainComplex A ℤ} (f : K ⟶ L)

/-- The original quotient followed by the explicit source-coordinate sign change. -/
def quotientToCone : middle f ⟶ mappingCone f :=
  quotientMap f ≫ (CochainComplex.mappingConeNegIso f).hom

/-- The unchanged inclusion and the explicitly transported quotient still compose to zero. -/
theorem inclusion_quotientToCone : inclusion f ≫ quotientToCone f = 0 := by
  simp [quotientToCone, ← Category.assoc]

/-- The short complex with original first map and the explicitly sign-adjusted cone quotient. -/
def quotientToConeSequence : ShortComplex (CochainComplex A ℤ) :=
  ShortComplex.mk (inclusion f) (quotientToCone f) (inclusion_quotientToCone f)

/-- The comparison retains both original first objects and the explicit cone sign isomorphism.
-/
def quotientToConeSequenceIso : quotientSequence f ≅ quotientToConeSequence f :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (CochainComplex.mappingConeNegIso f) (by simp [quotientSequence,
      quotientToConeSequence]) (by simp [quotientSequence, quotientToConeSequence, quotientToCone])

/-- Exactness is transported through that actual three-object isomorphism. -/
theorem quotientToConeSequence_shortExact : (quotientToConeSequence f).ShortExact :=
  ShortComplex.shortExact_of_iso (quotientToConeSequenceIso f) (quotientSequence_shortExact f)

end CochainComplex.SplitFactorization
