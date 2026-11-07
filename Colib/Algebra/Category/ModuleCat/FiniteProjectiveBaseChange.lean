/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.MatrixImageFunctor
public import Mathlib.CategoryTheory.Whiskering

/-!
Implementation provenance: Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd,
`Quillen/Aglib/Algebra/Category/ModuleCat/FiniteProjectiveBaseChange.lean`.
The original hypotheses and maps are retained.

# Change of rings for actual finite projective right modules

Transporting entrywise matrix change of rings along the proved image equivalence
gives functors for arbitrary ring homomorphisms. The identity and composition
comparisons are natural isomorphisms, because choosing presentations is not
strictly functorial on the underlying modules.
-/
@[expose] public section

noncomputable section

universe u v w

open CategoryTheory

namespace ModuleCat.FiniteProjective

variable {R : Type u} {S : Type v} {T : Type w} [Ring R] [Ring S] [Ring T]

/-- Change of rings on actual finite projective right modules via their proved matrix model. -/
def rightBaseChange (f : R →+* S) : Category.{u,u} Rᵐᵒᵖ ⥤ Category.{v,v} Sᵐᵒᵖ :=
  Matrix.RightModule.imageEquivalence.inverse ⋙ Matrix.RightModule.baseChange f ⋙
    Matrix.RightModule.imageEquivalence.functor

/-- Changing rings along the identity recovers the original module naturally. -/
def rightBaseChangeId : rightBaseChange (RingHom.id R) ≅ 𝟭 (Category.{u,u} Rᵐᵒᵖ) :=
  Matrix.RightModule.imageEquivalence.counitIso

/-- Consecutive changes of rings agree naturally with the composite ring homomorphism. -/
def rightBaseChangeComp (f : R →+* S) (g : S →+* T) :
    rightBaseChange f ⋙ rightBaseChange g ≅ rightBaseChange (g.comp f) :=
  Functor.isoWhiskerLeft Matrix.RightModule.imageEquivalence.inverse
    (Functor.isoWhiskerLeft (Matrix.RightModule.baseChange f)
      (Functor.isoWhiskerRight (Matrix.RightModule.imageEquivalence (R := S)).unitIso.symm
        (Matrix.RightModule.baseChange g ⋙ Matrix.RightModule.imageEquivalence.functor)))

end ModuleCat.FiniteProjective
