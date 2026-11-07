/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.StableFreeBaseChange
public import Colib.CategoryTheory.GroupCompletion.MonoidalFunctorNaturality
public import Colib.Topology.ClassifyingSpace.ProjectiveCompletionBaseChange
public import Colib.Topology.ClassifyingSpace.StableGeneralLinearRingNaturality

/-!
# Original matrix-to-completion naturality under change of rings

The prescribed finite-free comparisons give actual stage isomorphisms. Their
successor square uses the original tensorator and rank-one denominator
isomorphism. These squares assemble over the original matrix Grothendieck
construction, including its stabilization and its rank-zero unit comparison.

## Implementation provenance

Adapted from `Quillen/KTheory/Plus/StableCompletionBaseChangeNaturality.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, chosen paths, and original
proof hypotheses are retained under native ownership.
-/

@[expose] public section

open CategoryTheory.GroupCompletion
open CategoryTheory.GroupCompletion.ActionLocalization

noncomputable section
open Topology SSet HomotopyGroup
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalLeftAction
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  ModuleCat.FiniteProjective.categoryDirectSumMonoidal
  ModuleCat.FiniteProjective.directSumMonoidal
  ModuleCat.FiniteProjective.rightBaseChangeMonoidal
namespace ModuleCat.FiniteProjective.StableCompletion
open GroupCompletion GroupCompletion.ActionLocalization
variable {R S : Type u} [Ring R] [Ring S]

/-- Both coordinates use the prescribed comparison of the original rank-one powers. -/
def stageBaseChangeIso (f : R →+* S) (n : ℕ) :
    (completionBaseChange f).obj (stageObject R n) ≅ stageObject S n :=
  (ActionLocalization.ofFunctor (C := IsoCategory Sᵐᵒᵖ)).mapIso
    ((StableFree.powerBaseChangeIso f n).prod (StableFree.powerBaseChangeIso f n))

/-- The finite-stage square retains the actual matrix action in the second coordinate. -/
lemma stageBaseChangeIso_action (f : R →+* S) (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (completionBaseChange f).map ((stageAction R n g).asHom) ≫ (stageBaseChangeIso f n).hom =
      (stageBaseChangeIso f n).hom ≫
        (stageAction S n (StableGeneralLinear.finiteMap f n g)).asHom := by
  let F := (rightBaseChange f).core
  let P := rankOnePower Rᵐᵒᵖ n
  let Q := rankOnePower Sᵐᵒᵖ n
  let p := (StableFree.powerBaseChangeIso f n).hom
  change (GroupCompletion.monoidalMap F).map
      (ActionLocalization.ofHom (C := IsoCategory Rᵐᵒᵖ) (X := (P, P)) (Y := (P, P))
        (𝟙 P, (StableFree.powerEndEquiv R n g).asHom)) ≫
        ActionLocalization.ofHom (C := IsoCategory Sᵐᵒᵖ)
          (X := (F.obj P, F.obj P)) (Y := (Q, Q)) (p, p) =
    ActionLocalization.ofHom (C := IsoCategory Sᵐᵒᵖ)
      (X := (F.obj P, F.obj P)) (Y := (Q, Q)) (p, p) ≫
      ActionLocalization.ofHom (C := IsoCategory Sᵐᵒᵖ) (X := (Q, Q)) (Y := (Q, Q))
        (𝟙 Q, (StableFree.powerEndEquiv S n (StableGeneralLinear.finiteMap f n g)).asHom)
  rw [GroupCompletion.monoidalMap_ofHom, ← ActionLocalization.ofHom_comp,
    ← ActionLocalization.ofHom_comp]
  congr 1
  apply Prod.ext
  · change F.map (𝟙 P) ≫ p = p ≫ 𝟙 Q
    rw [F.map_id]
    exact (Category.id_comp p).trans (Category.comp_id p).symm
  · exact StableFree.powerBaseChangeIso_action f n g

/-- The original successor cocone square, with its actual rank-one denominator comparison. -/
lemma stageBaseChangeIso_successor (f : R →+* S) (n : ℕ) :
    (completionBaseChange f).map (stageArrow R n) ≫ (stageBaseChangeIso f (n + 1)).hom =
      (stageBaseChangeIso f n).hom ≫ stageArrow S n := by
  let F := (rightBaseChange f).core
  let P := rankOnePower Rᵐᵒᵖ n
  let Q := rankOnePower Sᵐᵒᵖ n
  let p : F.obj P ⟶ Q := (StableFree.powerBaseChangeIso f n).hom
  let q : F.obj (freeIso Rᵐᵒᵖ 1 ⊗ P) ⟶ freeIso Sᵐᵒᵖ 1 ⊗ Q :=
    (StableFree.powerBaseChangeIso f (n + 1)).hom
  change mkHom (C := IsoCategory Sᵐᵒᵖ)
      (X := (F.obj P, F.obj P))
      (Y := (F.obj (freeIso Rᵐᵒᵖ 1 ⊗ P), F.obj (freeIso Rᵐᵒᵖ 1 ⊗ P)))
      ⟨F.obj (freeIso Rᵐᵒᵖ 1),
        (Functor.LaxMonoidal.μ F (freeIso Rᵐᵒᵖ 1) P ≫ F.map (𝟙 _),
          Functor.LaxMonoidal.μ F (freeIso Rᵐᵒᵖ 1) P ≫ F.map (𝟙 _))⟩ ≫
        ActionLocalization.ofHom (C := IsoCategory Sᵐᵒᵖ)
          (X := (F.obj (freeIso Rᵐᵒᵖ 1 ⊗ P), F.obj (freeIso Rᵐᵒᵖ 1 ⊗ P)))
          (Y := (freeIso Sᵐᵒᵖ 1 ⊗ Q, freeIso Sᵐᵒᵖ 1 ⊗ Q)) (q, q) =
    ActionLocalization.ofHom (C := IsoCategory Sᵐᵒᵖ)
      (X := (F.obj P, F.obj P)) (Y := (Q, Q)) (p, p) ≫
      mkHom (C := IsoCategory Sᵐᵒᵖ) (X := (Q, Q))
        (Y := (freeIso Sᵐᵒᵖ 1 ⊗ Q, freeIso Sᵐᵒᵖ 1 ⊗ Q))
        ⟨freeIso Sᵐᵒᵖ 1, (𝟙 _, 𝟙 _)⟩
  rw [mkHom_comp_ofHom, ofHom_comp_mkHom]
  apply Quotient.sound
  refine ⟨Matrix.RightModule.freeCoreBaseChangeIso f 1, ?_⟩
  apply Prod.ext <;>
    change (Matrix.RightModule.freeCoreBaseChangeIso f 1).hom ▷ F.obj P ≫
        (freeIso Sᵐᵒᵖ 1 ◁ p ≫ 𝟙 _) =
      (Functor.LaxMonoidal.μ F (freeIso Rᵐᵒᵖ 1) P ≫ F.map (𝟙 _)) ≫
        q
  all_goals
    simp only [F.map_id, Category.comp_id]
    rw [← tensorHom_def]
    exact (StableFree.powerBaseChangeIso_successor f n).symm

/-- The specified stage comparisons commute with every original rank transition. -/
lemma stageBaseChangeIso_transition (f : R →+* S) {n m : ℕ} (h : n ≤ m) :
    (completionBaseChange f).map ((stageSequence R).map (homOfLE h)) ≫
        (stageBaseChangeIso f m).hom =
      (stageBaseChangeIso f n).hom ≫ (stageSequence S).map (homOfLE h) := by
  induction h using Nat.leRec with
  | refl =>
    change (completionBaseChange f).map ((stageSequence R).map (𝟙 n)) ≫ _ =
      _ ≫ (stageSequence S).map (𝟙 n)
    rw [(stageSequence R).map_id, (stageSequence S).map_id, (completionBaseChange f).map_id]
    simp
  | @le_succ_of_le m h ih =>
    rw [← homOfLE_comp h (Nat.le_succ m), Functor.map_comp, Functor.map_comp,
      Functor.map_comp]
    rw [show (stageSequence R).map (homOfLE (Nat.le_succ m)) = stageArrow R m from
      Functor.ofSequence_map_homOfLE_succ _ m]
    rw [show (stageSequence S).map (homOfLE (Nat.le_succ m)) = stageArrow S m from
      Functor.ofSequence_map_homOfLE_succ _ m]
    rw [Category.assoc, stageBaseChangeIso_successor, ← Category.assoc, ih, Category.assoc]

/-- Change of rings commutes with the original telescope completion map by this actual iso. -/
def telescopeBaseChangeIso (f : R →+* S) :
    telescopeFunctor R ⋙ completionBaseChange f ≅
      StableGeneralLinear.GrothendieckModel.ringFunctor f ⋙ telescopeFunctor S :=
  NatIso.ofComponents
    (fun X => stageBaseChangeIso f (StableGeneralLinear.rank X.base)) (by
    intro X Y a
    change (completionBaseChange f).map
        ((stageSequence R).map (AsSmall.down.map a.base) ≫
          (stageAction R (StableGeneralLinear.rank Y.base) a.fiber.down).asHom) ≫
        (stageBaseChangeIso f (StableGeneralLinear.rank Y.base)).hom =
      (stageBaseChangeIso f (StableGeneralLinear.rank X.base)).hom ≫
        (stageSequence S).map (AsSmall.down.map a.base) ≫
          (stageAction S (StableGeneralLinear.rank Y.base)
            ((StableGeneralLinear.GrothendieckModel.ringFunctor f).map a).fiber.down).asHom
    rw [StableGeneralLinear.GrothendieckModel.ringFunctor_map_fiber,
      Functor.map_comp, Category.assoc, stageBaseChangeIso_action, ← Category.assoc,
      stageBaseChangeIso_transition f (leOfHom (AsSmall.down.map a.base)), Category.assoc])

/-- The rank-zero component is exactly the original completion unit-comparison isomorphism. -/
lemma stageBaseChangeIso_zero (f : R →+* S) :
    stageBaseChangeIso f 0 = completionBaseChangeZeroIso f := by
  simp only [stageBaseChangeIso, StableFree.powerBaseChangeIso_zero]
  rfl

end ModuleCat.FiniteProjective.StableCompletion
