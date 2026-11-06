/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Algebra.Homology.MappingCone.Identity
public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.RelativeComplex

/-! # The actual zero-source cylinder endpoint

The cylinder projection on an arrow with a genuinely zero source is an actual
isomorphism, whose inverse is the original target section. Its naturality
is the existing cylinder naturality, not an assumed normalization.
-/
/-! Adapted from `Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.ZeroEndpoint`
at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CochainComplex








noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
universe v u w t

namespace CochainComplex.SplitFactorization
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The original projection and section are mutually inverse on zero sources. -/
def projectionIsoOfIsZeroSource {K L : CochainComplex A ℤ} (f : K ⟶ L)
    (hK : IsZero K) : middle f ≅ L where
  hom := projection f
  inv := biprod.inr
  hom_inv_id := by
    apply biprod.hom_ext'
    · exact (identityCone_isZero hK).eq_of_src _ _
    · simp [projection]
  inv_hom_id := by simp [projection]

@[simp]
theorem projectionIsoOfIsZeroSource_hom {K L : CochainComplex A ℤ} (f : K ⟶ L)
    (hK : IsZero K) : (projectionIsoOfIsZeroSource f hK).hom = projection f := rfl

@[simp]
theorem projectionIsoOfIsZeroSource_inv {K L : CochainComplex A ℤ} (f : K ⟶ L)
    (hK : IsZero K) :
    (projectionIsoOfIsZeroSource f hK).inv = (biprod.inr : L ⟶ middle f) := rfl

/-- For every actual family of zero-source arrows the original cylinder
projection is a natural isomorphism to the actual target family. -/
def zeroSourceProjectionNatIso {J : Type t} [Category.{w} J]
    (F : J ⥤ Arrow (CochainComplex A ℤ)) (hF : ∀ j, IsZero (F.obj j).left) :
    F ⋙ middleFunctor ≅ F ⋙ Arrow.rightFunc :=
  NatIso.ofComponents (fun j ↦ projectionIsoOfIsZeroSource (F.obj j).hom (hF j))
    (fun {_ _} f ↦ projection_naturality (F.map f))

@[simp]
theorem zeroSourceProjectionNatIso_hom {J : Type t} [Category.{w} J]
    (F : J ⥤ Arrow (CochainComplex A ℤ)) (hF : ∀ j, IsZero (F.obj j).left) (j : J) :
    (zeroSourceProjectionNatIso F hF).hom.app j = projection (F.obj j).hom := rfl

end CochainComplex.SplitFactorization
