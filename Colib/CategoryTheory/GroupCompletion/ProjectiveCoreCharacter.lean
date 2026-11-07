/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.ProjectiveAutomorphismAdditivity
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveMonoidal

/-!
Implementation provenance: `Quillen/CategoryTheory/GroupCompletion/ProjectiveCoreCharacter.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# The additive stable matrix character on the actual projective core

The character uses the original direct-sum monoidal groupoid and the actual
stable elementary quotient, preserving conjugation and both translations.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  ModuleCat.FiniteProjective.categoryDirectSumMonoidal
  ModuleCat.FiniteProjective.directSumMonoidal
namespace ModuleCat.FiniteProjective
variable {R : Type u} [Ring R]

/-- The original stable matrix character of the actual core endomorphism group. -/
def coreCharacter (P : IsoCategory Rᵐᵒᵖ) :
    End P →* StableGeneralLinear.ElementaryQuotient R where
  toFun g := Matrix.RightModule.projectiveAutomorphismClass P.of g.iso
  map_one' := map_one (Matrix.RightModule.projectiveAutomorphismClass P.of)
  map_mul' g h := (Matrix.RightModule.projectiveAutomorphismClass P.of).map_mul g.iso h.iso

/-- Transport along any actual projective isomorphism preserves the character. -/
lemma coreCharacter_conjugate {P Q : IsoCategory Rᵐᵒᵖ} (f : P ⟶ Q) (g : End P) :
    coreCharacter Q (inv f ≫ g ≫ f) = coreCharacter P g := by
  rw [← Groupoid.inv_eq_inv]
  exact Matrix.RightModule.projectiveAutomorphismClass_conjugate f.iso g.iso

/-- The character takes the original monoidal direct sum to multiplication. -/
lemma coreCharacter_tensor (P Q : IsoCategory Rᵐᵒᵖ) (g : End P) (h : End Q) :
    coreCharacter (P ⊗ Q) (g ⊗ₘ h) = coreCharacter P g * coreCharacter Q h := by
  exact Matrix.RightModule.projectiveAutomorphismClass_coprod P.of Q.of g.iso h.iso

/-- The original left translation fixes the stable character. -/
lemma coreCharacter_whiskerLeft (P Q : IsoCategory Rᵐᵒᵖ) (g : End Q) :
    coreCharacter (P ⊗ Q) (P ◁ g) = coreCharacter Q g := by
  rw [← id_tensorHom, coreCharacter_tensor]
  change coreCharacter P 1 * coreCharacter Q g = _
  rw [map_one, one_mul]

/-- The original right translation fixes the stable character. -/
lemma coreCharacter_whiskerRight (P Q : IsoCategory Rᵐᵒᵖ) (g : End P) :
    coreCharacter (P ⊗ Q) (g ▷ Q) = coreCharacter P g := by
  rw [← tensorHom_id, coreCharacter_tensor]
  change coreCharacter P g * coreCharacter Q 1 = _
  rw [map_one, mul_one]

end ModuleCat.FiniteProjective
