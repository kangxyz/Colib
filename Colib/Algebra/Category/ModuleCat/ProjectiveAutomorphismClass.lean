/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.LinearAlgebra.Matrix.IdempotentAutomorphismClass
public import Colib.Algebra.Category.ModuleCat.MatrixImageFunctor

/-!
Implementation provenance: `Quillen/Algebra/Category/ModuleCat/ProjectiveAutomorphismClass.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Stable matrix classes of actual projective automorphisms

The actual matrix-image equivalence transports the proved presentation-invariant
class to finite projective right modules. Every image presentation computes the
same class, so the chosen inverse-equivalence presentation is immaterial.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory
namespace Matrix.RightModule
variable {R : Type u} [Ring R]

/-- Stable elementary-quotient class of an actual finite projective right-module automorphism. -/
def projectiveAutomorphismClass (P : ModuleCat.FiniteProjective.Category.{u, u} Rᵐᵒᵖ) :
    Aut P →* StableGeneralLinear.ElementaryQuotient R :=
  (automorphismClass ((imageEquivalence (R := R)).inverse.obj P)).comp
    (Functor.mapAut P (imageEquivalence (R := R)).inverse)

/-- Actual isomorphisms of projective modules preserve their stable automorphism classes. -/
lemma projectiveAutomorphismClass_conjugate
    {P Q : ModuleCat.FiniteProjective.Category.{u, u} Rᵐᵒᵖ} (e : P ≅ Q) (g : Aut P) :
    projectiveAutomorphismClass Q (Aut.autMulEquivOfIso e g) =
      projectiveAutomorphismClass P g := by
  apply (automorphismClass_presentation ((imageEquivalence (R := R)).inverse.mapIso e)
    ((imageEquivalence (R := R)).inverse.mapAut _ g) _ ?_).symm
  change (imageEquivalence (R := R)).inverse.map e.inv ≫
    (imageEquivalence (R := R)).inverse.map g.asIso.hom =
      (imageEquivalence (R := R)).inverse.map (e.inv ≫ g.asIso.hom ≫ e.hom) ≫
        (imageEquivalence (R := R)).inverse.map e.inv
  simp [← Functor.map_comp]

/-- Every original matrix-image presentation computes precisely the same actual module class. -/
lemma projectiveAutomorphismClass_image (P : ProjectiveMatrices R) (g : Aut P) :
    projectiveAutomorphismClass (imageFunctor.obj P) (imageFunctor.mapAut _ g) =
      automorphismClass P g := by
  apply (automorphismClass_presentation
    ((imageEquivalence (R := R)).unitIso.app P) g _ ?_).symm
  exact ((imageEquivalence (R := R)).unitIso.inv.naturality g.asIso.hom).symm

/-- Any image presentation and realization isomorphism computes the same value. -/
lemma projectiveAutomorphismClass_presentation
    (P : ProjectiveMatrices R) (M : ModuleCat.FiniteProjective.Category.{u, u} Rᵐᵒᵖ)
    (e : imageFunctor.obj P ≅ M) (g : Aut P) :
    projectiveAutomorphismClass M (Aut.autMulEquivOfIso e (imageFunctor.mapAut _ g)) =
      automorphismClass P g := by
  rw [projectiveAutomorphismClass_conjugate, projectiveAutomorphismClass_image]

end Matrix.RightModule
