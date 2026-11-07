/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.StableFreeDiagram
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeFreeCoherence

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/StableFreeBaseChange.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Change of rings on the original reversal-aligned free sequence

The prescribed finite-free comparison is transported through the original
rank-one-power identifications. Its matrix-action and successor squares retain
both the explicit finite reversal and the original coproduct tensorator.
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
  ModuleCat.FiniteProjective.rightBaseChangeMonoidal
namespace ModuleCat.FiniteProjective.StableFree
variable {R S : Type u} [Ring R] [Ring S]

/-- The original finite-free comparison retains the reversal-aligned matrix action. -/
lemma freeCoreBaseChangeIso_action (f : R →+* S) (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (rightBaseChange f).core.map (freeEndEquiv R n g) ≫
        (Matrix.RightModule.freeCoreBaseChangeIso f n).hom =
      (Matrix.RightModule.freeCoreBaseChangeIso f n).hom ≫
        freeEndEquiv S n (StableGeneralLinear.finiteMap f n g) := by
  apply Core.hom_ext
  exact Matrix.RightModule.freeBaseChangeIso_left_action f n g

/-- The actual comparison on the chosen left rank-one powers. -/
def powerBaseChangeIso (f : R →+* S) (n : ℕ) :
    (rightBaseChange f).core.obj (rankOnePower Rᵐᵒᵖ n) ≅ rankOnePower Sᵐᵒᵖ n :=
  (rightBaseChange f).core.mapIso (rankOnePowerIsoFree Rᵐᵒᵖ n) ≪≫
    Matrix.RightModule.freeCoreBaseChangeIso f n ≪≫ (rankOnePowerIsoFree Sᵐᵒᵖ n).symm

/-- Every original finite matrix square commutes through the chosen power comparison. -/
lemma powerBaseChangeIso_action (f : R →+* S) (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (rightBaseChange f).core.map (powerEndEquiv R n g) ≫ (powerBaseChangeIso f n).hom =
      (powerBaseChangeIso f n).hom ≫
        powerEndEquiv S n (StableGeneralLinear.finiteMap f n g) := by
  let F := (rightBaseChange f).core
  change F.map ((rankOnePowerIsoFree Rᵐᵒᵖ n).hom ≫ freeEndEquiv R n g ≫
      (rankOnePowerIsoFree Rᵐᵒᵖ n).inv) ≫
        (F.map (rankOnePowerIsoFree Rᵐᵒᵖ n).hom ≫
          (Matrix.RightModule.freeCoreBaseChangeIso f n).hom ≫
            (rankOnePowerIsoFree Sᵐᵒᵖ n).inv) =
    (F.map (rankOnePowerIsoFree Rᵐᵒᵖ n).hom ≫
      (Matrix.RightModule.freeCoreBaseChangeIso f n).hom ≫
        (rankOnePowerIsoFree Sᵐᵒᵖ n).inv) ≫
      (rankOnePowerIsoFree Sᵐᵒᵖ n).hom ≫
        freeEndEquiv S n (StableGeneralLinear.finiteMap f n g) ≫
          (rankOnePowerIsoFree Sᵐᵒᵖ n).inv
  simp only [Functor.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc,
    Iso.inv_hom_id_assoc]
  rw [reassoc_of% freeCoreBaseChangeIso_action f n g]

/-- The successor square uses the actual strong-monoidal tensorator and rank-one comparison. -/
lemma powerBaseChangeIso_successor (f : R →+* S) (n : ℕ) :
    Functor.LaxMonoidal.μ (rightBaseChange f).core
        (freeIso Rᵐᵒᵖ 1) (rankOnePower Rᵐᵒᵖ n) ≫
          (powerBaseChangeIso f (n + 1)).hom =
      (Matrix.RightModule.freeCoreBaseChangeIso f 1).hom ⊗ₘ (powerBaseChangeIso f n).hom := by
  let F := (rightBaseChange f).core
  simp only [powerBaseChangeIso, rankOnePowerIsoFree, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.trans_inv, tensorIso_hom, tensorIso_inv, Iso.refl_hom, Iso.refl_inv,
    Functor.map_comp, Category.assoc]
  rw [← reassoc_of% Functor.LaxMonoidal.μ_natural F
    (𝟙 (freeIso Rᵐᵒᵖ 1)) (rankOnePowerIsoFree Rᵐᵒᵖ n).hom]
  rw [reassoc_of% Matrix.RightModule.freeCoreBaseChangeIso_successor f n]
  simp only [F.map_id, Iso.hom_inv_id_assoc,
    tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  rfl

/-- At zero, the actual power comparison is the original inverse unit comparison. -/
lemma powerBaseChangeIso_zero (f : R →+* S) :
    powerBaseChangeIso f 0 = (Functor.Monoidal.εIso (rightBaseChange f).core).symm := by
  apply Iso.ext
  apply Core.hom_ext
  apply (cancel_epi (Functor.LaxMonoidal.ε (rightBaseChange f))).1
  exact initial.hom_ext _ _

end ModuleCat.FiniteProjective.StableFree
