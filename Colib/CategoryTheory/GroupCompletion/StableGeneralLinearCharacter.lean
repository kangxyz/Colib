/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.FramedCharacterExtension
public import Colib.CategoryTheory.GroupCompletion.ProjectiveCoreCharacterMatrices
public import Colib.CategoryTheory.GroupCompletion.StableGeneralLinearMap

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/StableGeneralLinearCharacter.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# The original stable matrix quotient character on the completion comparison

The genuine projective character extends over the entire original completion
category. Its restriction to the finite-matrix telescope retains the actual
stable quotient projection, with its original stabilization arrows.
-/
@[expose] public section

open CategoryTheory.GroupCompletion.Localization

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  ModuleCat.FiniteProjective.categoryDirectSumMonoidal
  ModuleCat.FiniteProjective.directSumMonoidal
  ModuleCat.FiniteProjective.directSumSymmetric
namespace ModuleCat.FiniteProjective.StableCompletion
open GroupCompletion.Localization
variable (R : Type u) [Ring R]

/-- The actual projective character on the original completion category. -/
def stableCompletionCharacter : Completion R ⥤
    SingleObj (StableGeneralLinear.ElementaryQuotient R) :=
  completionCharacter coreCharacter (fun f g => coreCharacter_conjugate f g)
    coreCharacter_whiskerLeft

/-- The finite-matrix telescope has its original identity frame at every rank. -/
def telescopeFramedFunctor : StableGeneralLinear.GrothendieckModel.Telescope R ⥤
    FramedPair (IsoCategory Rᵐᵒᵖ) where
  obj X := diagonalFrame (rankOnePower Rᵐᵒᵖ (StableGeneralLinear.rank X.base))
  map f := (telescopeFunctor R).map f
  map_id X := (telescopeFunctor R).map_id X
  map_comp f g := (telescopeFunctor R).map_comp f g

/-- The original stage sequence with the actual diagonal frames. -/
def framedStageSequence : ℕ ⥤ FramedPair (IsoCategory Rᵐᵒᵖ) where
  obj n := diagonalFrame (rankOnePower Rᵐᵒᵖ n)
  map f := (stageSequence R).map f
  map_id n := (stageSequence R).map_id n
  map_comp f g := (stageSequence R).map_comp f g

/-- The chosen projective character on the actual framed category. -/
abbrev stableFramedCharacter :=
  framedCharacter (coreCharacter (R := R)) (fun f g => coreCharacter_conjugate f g)
    coreCharacter_whiskerLeft

/-- Every original finite stabilization arrow has trivial framed character. -/
lemma stableFramedCharacter_stageSequence {n m : ℕ} (h : n ≤ m) :
    (stableFramedCharacter R).map ((framedStageSequence R).map (homOfLE h)) =
      (1 : StableGeneralLinear.ElementaryQuotient R) := by
  induction m, h using Nat.le_induction with
  | base =>
    change (stableFramedCharacter R).map ((framedStageSequence R).map (𝟙 n)) = 1
    rw [(framedStageSequence R).map_id, (stableFramedCharacter R).map_id]
    rfl
  | succ m hm ih =>
    rw [← homOfLE_comp hm (Nat.le_succ m), (framedStageSequence R).map_comp,
      (stableFramedCharacter R).map_comp]
    change @Mul.mul (StableGeneralLinear.ElementaryQuotient R) _
      ((stableFramedCharacter R).map ((framedStageSequence R).map
        (homOfLE (Nat.le_succ m))))
        ((stableFramedCharacter R).map ((framedStageSequence R).map (homOfLE hm))) = 1
    rw [ih]
    refine (mul_one (M := StableGeneralLinear.ElementaryQuotient R) _).trans ?_
    change (stableFramedCharacter R).map
      (show diagonalFrame (rankOnePower Rᵐᵒᵖ m) ⟶
        diagonalFrame (rankOnePower Rᵐᵒᵖ (m + 1)) from
          (stageSequence R).map (homOfLE (Nat.le_succ m))) =
      (1 : StableGeneralLinear.ElementaryQuotient R)
    rw [show (stageSequence R).map (homOfLE (Nat.le_succ m)) = stageArrow R m from
      Functor.ofSequence_map_homOfLE_succ _ m]
    exact framedCharacter_translation _ _ _ (freeIso Rᵐᵒᵖ 1) (rankOnePower Rᵐᵒᵖ m)

/-- On the original fiber matrix action the framed character is the actual quotient projection. -/
lemma stableFramedCharacter_stageAction (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (stableFramedCharacter R).map
      (show diagonalFrame (rankOnePower Rᵐᵒᵖ n) ⟶ diagonalFrame (rankOnePower Rᵐᵒᵖ n) from
        (stageAction R n g).asHom) = StableGeneralLinear.finiteClass R n g := by
  exact (framedCharacter_numerator _ _ _ _ (StableFree.powerEndEquiv R n g)).trans
    (coreCharacter_powerEndEquiv R n g)

/-- The quotient projection on the original stable single-object category. -/
def quotientCategoryFunctor : StableGeneralLinear.stableCategory R ⥤
    SingleObj (StableGeneralLinear.ElementaryQuotient R) :=
  AsSmall.down ⋙ (StableGeneralLinear.quotientMap R).toFunctor

/-- The framed telescope character is exactly the original quotient after the actual projection. -/
lemma telescopeFramed_character :
    telescopeFramedFunctor R ⋙ stableFramedCharacter R =
      StableGeneralLinear.GrothendieckModel.projection R ⋙ quotientCategoryFunctor R := by
  refine CategoryTheory.Functor.ext
    (F := telescopeFramedFunctor R ⋙ stableFramedCharacter R)
    (G := StableGeneralLinear.GrothendieckModel.projection R ⋙ quotientCategoryFunctor R)
    (fun _ => Subsingleton.elim _ _) ?_
  intro X Y f
  simp only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id]
  change (stableFramedCharacter R).map
    ((framedStageSequence R).map (AsSmall.down.map f.base) ≫
      (show diagonalFrame (rankOnePower Rᵐᵒᵖ (StableGeneralLinear.rank Y.base)) ⟶
        diagonalFrame (rankOnePower Rᵐᵒᵖ (StableGeneralLinear.rank Y.base)) from
          (stageAction R (StableGeneralLinear.rank Y.base) f.fiber.down).asHom)) = _
  rw [(stableFramedCharacter R).map_comp]
  change @Mul.mul (StableGeneralLinear.ElementaryQuotient R) _
    ((stableFramedCharacter R).map _) ((stableFramedCharacter R).map _) = _
  rw [stableFramedCharacter_stageAction]
  have hb : AsSmall.down.map f.base = homOfLE (leOfHom (AsSmall.down.map f.base)) :=
    Subsingleton.elim _ _
  rw [hb, stableFramedCharacter_stageSequence]
  exact mul_one (M := StableGeneralLinear.ElementaryQuotient R) _

/-- The global actual character has the original stable quotient as its telescope restriction. -/
def telescopeCharacterIso : telescopeFunctor R ⋙ stableCompletionCharacter R ≅
    StableGeneralLinear.GrothendieckModel.projection R ⋙ quotientCategoryFunctor R :=
  (Functor.isoWhiskerLeft (telescopeFramedFunctor R)
    (completionCharacterIso coreCharacter (fun f g => coreCharacter_conjugate f g)
      coreCharacter_whiskerLeft)) ≪≫ eqToIso (telescopeFramed_character R)

end ModuleCat.FiniteProjective.StableCompletion
