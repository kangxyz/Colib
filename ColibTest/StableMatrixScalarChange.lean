/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.CategoryTheory.GroupCompletion.StableFreeBaseChange
import Colib.CategoryTheory.GroupCompletion.MonoidalFunctorNaturality

/-!
# Original scalar-change squares and completion coherence

The coefficient rings need not be commutative. These tests retain rectangular
matrix entries, the explicit basis reversal, the original power tensorator,
and the actual identity and composition comparisons on completion categories.
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open ModuleCat.FiniteProjective
open scoped Matrix
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal rightBaseChangeMonoidal

variable {R S T : Type u} [Ring R] [Ring S] [Ring T]

example {n m : ℕ} (A : Matrix (Fin m) (Fin n) R)
    (x : Fin n → Rᵐᵒᵖ) (i : Fin m) :
    (Matrix.RightModule.freeRectHom A).hom x i =
      MulOpposite.op ((A *ᵥ fun j => MulOpposite.unop (x j)) i) :=
  Matrix.RightModule.freeRectHom_apply A x i

example (f : R →+* S) {n m : ℕ} (A : Matrix (Fin m) (Fin n) R) :
    (rightBaseChange f).map (Matrix.RightModule.freeRectHom A) ≫
        (Matrix.RightModule.freeBaseChangeIso f m).hom =
      (Matrix.RightModule.freeBaseChangeIso f n).hom ≫
        Matrix.RightModule.freeRectHom (A.map f) :=
  Matrix.RightModule.freeBaseChangeIso_rect_naturality f A

example (f : R →+* S) (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (rightBaseChange f).core.map (StableFree.powerEndEquiv R n g) ≫
        (StableFree.powerBaseChangeIso f n).hom =
      (StableFree.powerBaseChangeIso f n).hom ≫
        StableFree.powerEndEquiv S n (StableGeneralLinear.finiteMap f n g) :=
  StableFree.powerBaseChangeIso_action f n g

example (f : R →+* S) (n : ℕ) :
    Functor.LaxMonoidal.μ (rightBaseChange f).core
        (freeIso Rᵐᵒᵖ 1) (rankOnePower Rᵐᵒᵖ n) ≫
          (StableFree.powerBaseChangeIso f (n + 1)).hom =
      (Matrix.RightModule.freeCoreBaseChangeIso f 1).hom ⊗ₘ
        (StableFree.powerBaseChangeIso f n).hom :=
  StableFree.powerBaseChangeIso_successor f n

example (f : R →+* S) :
    StableFree.powerBaseChangeIso f 0 =
      (Functor.Monoidal.εIso (rightBaseChange f).core).symm :=
  StableFree.powerBaseChangeIso_zero f

example (f : R →+* S) :
    GroupCompletion.Localization.unitEntry (C := IsoCategory Rᵐᵒᵖ) ⋙
        GroupCompletion.monoidalMap (rightBaseChangeCore f) ≅
      rightBaseChangeCore f ⋙ GroupCompletion.Localization.unitEntry :=
  GroupCompletion.monoidalMapUnitIso (rightBaseChangeCore f)

example : GroupCompletion.monoidalMap (rightBaseChangeCore (RingHom.id R)) ≅
    𝟭 (GroupCompletion.Localization (IsoCategory Rᵐᵒᵖ) (IsoCategory Rᵐᵒᵖ)) :=
  GroupCompletion.monoidalMapIso rightBaseChangeCoreId ≪≫
    eqToIso GroupCompletion.monoidalMap_id

example (f : R →+* S) (g : S →+* T) :
    GroupCompletion.monoidalMap (rightBaseChangeCore f) ⋙
        GroupCompletion.monoidalMap (rightBaseChangeCore g) ≅
      GroupCompletion.monoidalMap (rightBaseChangeCore (g.comp f)) :=
  eqToIso (GroupCompletion.monoidalMap_comp (rightBaseChangeCore f) (rightBaseChangeCore g)) ≪≫
    GroupCompletion.monoidalMapIso (rightBaseChangeCoreComp f g)
