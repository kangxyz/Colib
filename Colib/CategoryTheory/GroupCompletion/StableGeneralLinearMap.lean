/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.StableFreeDiagram
public import Colib.CategoryTheory.GroupCompletion.DiagonalAction
public import Colib.CategoryTheory.GroupCompletion.ActionTranslationNaturality
public import Colib.Topology.ClassifyingSpace.StableGeneralLinearGrothendieck

/-!
Implementation provenance: `Quillen/CategoryTheory/GroupCompletion/StableGeneralLinearMap.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Original finite matrix arrows in the projective group-completion category

The rank-n object is the pair of actual rank-one powers. A matrix acts on the
second coordinate, and successor arrows are the original common-denominator
translations. The resulting coherent system retains the finite-stage maps.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalLeftAction
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  ModuleCat.FiniteProjective.categoryDirectSumMonoidal
  ModuleCat.FiniteProjective.directSumMonoidal

namespace ModuleCat.FiniteProjective.StableCompletion
variable (R : Type u) [Ring R]

/-- The actual Grayson category of finite projective right modules. -/
abbrev Completion := GroupCompletion.Localization (IsoCategory Rᵐᵒᵖ) (IsoCategory Rᵐᵒᵖ)

/-- The equal-power pair representing the rank-n zero-component base object. -/
abbrev stageObject (n : ℕ) : Completion R :=
  ⟨rankOnePower Rᵐᵒᵖ n, rankOnePower Rᵐᵒᵖ n⟩

/-- A matrix acts on the second coordinate of the original equal-power pair. -/
def pairAction (n : ℕ) : Matrix.GeneralLinearGroup (Fin n) R →*
    End (rankOnePower Rᵐᵒᵖ n, rankOnePower Rᵐᵒᵖ n) where
  toFun g := End.of (𝟙 _, (StableFree.powerEndEquiv R n g).asHom)
  map_one' := by
    apply End.ext
    change (𝟙 (rankOnePower Rᵐᵒᵖ n), (StableFree.powerEndEquiv R n 1).asHom) =
      (𝟙 (rankOnePower Rᵐᵒᵖ n), 𝟙 (rankOnePower Rᵐᵒᵖ n))
    refine Prod.ext rfl ?_
    exact congrArg End.asHom (map_one (StableFree.powerEndEquiv R n))
  map_mul' g h := End.ext (Prod.ext (Category.id_comp _).symm
    (congrArg End.asHom (map_mul (StableFree.powerEndEquiv R n) g h)))

/-- The original finite-stage matrix action in the group-completion category. -/
def stageAction (n : ℕ) : Matrix.GeneralLinearGroup (Fin n) R →* End (stageObject R n) :=
  (GroupCompletion.ActionLocalization.ofFunctor (C := IsoCategory Rᵐᵒᵖ)).mapEnd _ |>.comp
    (pairAction R n)

/-- Successor ranks are joined by the original diagonal rank-one translation. -/
def stageArrow (n : ℕ) : stageObject R n ⟶ stageObject R (n + 1) :=
  GroupCompletion.ActionLocalization.translation (freeIso Rᵐᵒᵖ 1)
    (rankOnePower Rᵐᵒᵖ n, rankOnePower Rᵐᵒᵖ n)

/-- The original successor square intertwines matrix stabilization. -/
lemma stageAction_step (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (stageAction R n g).asHom ≫ stageArrow R n =
      stageArrow R n ≫ (stageAction R (n + 1) (StableGeneralLinear.step R n g)).asHom := by
  dsimp only [stageAction, stageArrow, stageObject, MonoidHom.comp_apply, Functor.mapEnd]
  change GroupCompletion.ActionLocalization.ofHom (pairAction R n g).asHom ≫ _ = _
  rw [GroupCompletion.ActionLocalization.ofHom_translation]
  congr 1
  apply congrArg GroupCompletion.ActionLocalization.ofHom
  apply Prod.ext
  · change freeIso Rᵐᵒᵖ 1 ◁ 𝟙 (rankOnePower Rᵐᵒᵖ n) =
      𝟙 (freeIso Rᵐᵒᵖ 1 ⊗ rankOnePower Rᵐᵒᵖ n)
    exact MonoidalCategory.whiskerLeft_id (freeIso Rᵐᵒᵖ 1) (rankOnePower Rᵐᵒᵖ n)
  · change (tensorLeft (freeIso Rᵐᵒᵖ 1)).map (StableFree.powerEndEquiv R n g).asHom =
      (StableFree.powerEndEquiv R (n + 1) (StableGeneralLinear.step R n g)).asHom
    exact congrArg End.asHom (StableFree.powerEndEquiv_step R n g).symm

/-- The sequence of original common-denominator successor arrows. -/
abbrev stageSequence : ℕ ⥤ Completion R where
  obj := stageObject R
  map {n m} f := Functor.OfSequence.map (stageArrow R) n m (leOfHom f)
  map_id n := Functor.OfSequence.map_id (stageArrow R) n
  map_comp f g := Functor.OfSequence.map_comp (stageArrow R) _ _ _ (leOfHom f) (leOfHom g)

/-- All finite-rank transition squares follow from the original successor square. -/
lemma stageAction_transition {n m : ℕ} (h : n ≤ m) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (stageAction R n g).asHom ≫ (stageSequence R).map (homOfLE h) =
      (stageSequence R).map (homOfLE h) ≫
        (stageAction R m (StableGeneralLinear.transition R n m h g)).asHom := by
  induction h using Nat.leRec with
  | refl =>
    rw [StableGeneralLinear.transition_self]
    change _ ≫ (stageSequence R).map (𝟙 n) = (stageSequence R).map (𝟙 n) ≫ _
    rw [(stageSequence R).map_id n]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  | @le_succ_of_le m h ih =>
    rw [← homOfLE_comp h (Nat.le_succ m), Functor.map_comp]
    rw [show (stageSequence R).map (homOfLE (Nat.le_succ m)) = stageArrow R m from
      Functor.ofSequence_map_homOfLE_succ _ m]
    rw [← Category.assoc, ih, Category.assoc, stageAction_step, ← Category.assoc,
      StableGeneralLinear.transition_step]

/-- The actual finite-stage functor, using the common-universe matrix category. -/
def stageFunctor (n : ℕ) : StableGeneralLinear.finiteCategory R n ⥤ Completion R :=
  AsSmall.down ⋙ SingleObj.functor (stageAction R n)

/-- The original stage-translation arrows form the required lax cocone. -/
def stageTransformation {i j : StableGeneralLinear.RankIndex.{u}} (f : i ⟶ j) :
    stageFunctor R (StableGeneralLinear.rank i) ⟶
      ((StableGeneralLinear.categoryDiagram R).map f).toFunctor ⋙
        stageFunctor R (StableGeneralLinear.rank j) where
  app _ := (stageSequence R).map (AsSmall.down.map f)
  naturality _ _ g := stageAction_transition R (leOfHom (AsSmall.down.map f)) g.down

private lemma fiber_id (X : StableGeneralLinear.GrothendieckModel.Telescope R) :
    (𝟙 X : X ⟶ X).fiber.down =
      (1 : Matrix.GeneralLinearGroup (Fin (StableGeneralLinear.rank X.base)) R) := by
  rcases X with ⟨x, ⟨⟨⟩⟩⟩
  rfl

private lemma fiber_comp {X Y Z : StableGeneralLinear.GrothendieckModel.Telescope R}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).fiber.down =
      @Mul.mul (Matrix.GeneralLinearGroup (Fin (StableGeneralLinear.rank Z.base)) R) _ g.fiber.down
        (StableGeneralLinear.transition R _ _
          (leOfHom (AsSmall.down.map g.base)) f.fiber.down) := by
  rcases X with ⟨x, ⟨⟨⟩⟩⟩
  rcases Y with ⟨y, ⟨⟨⟩⟩⟩
  rcases Z with ⟨z, ⟨⟨⟩⟩⟩
  exact mul_one (M := Matrix.GeneralLinearGroup (Fin (StableGeneralLinear.rank z)) R) _

/-- The coherent original finite-stage maps define a functor on the actual Grothendieck model. -/
def telescopeFunctor : StableGeneralLinear.GrothendieckModel.Telescope R ⥤ Completion R where
  obj X := stageObject R (StableGeneralLinear.rank X.base)
  map {X Y} f := (stageSequence R).map (AsSmall.down.map f.base) ≫
    (stageAction R (StableGeneralLinear.rank Y.base) f.fiber.down).asHom
  map_id X := by
    rw [CategoryTheory.Grothendieck.id_base, fiber_id, map_one]
    change (stageSequence R).map (𝟙 (StableGeneralLinear.rank X.base)) ≫ 𝟙 _ = 𝟙 _
    exact (Category.comp_id _).trans ((stageSequence R).map_id _)
  map_comp {X Y Z} f g := by
    let a : Matrix.GeneralLinearGroup (Fin (StableGeneralLinear.rank Y.base)) R := f.fiber.down
    let b : Matrix.GeneralLinearGroup (Fin (StableGeneralLinear.rank Z.base)) R := g.fiber.down
    let h := leOfHom (AsSmall.down.map g.base)
    have hc : (stageAction R (StableGeneralLinear.rank Z.base) (f ≫ g).fiber.down).asHom =
        (stageAction R (StableGeneralLinear.rank Z.base)
          (StableGeneralLinear.transition R _ _ h a)).asHom ≫
            (stageAction R (StableGeneralLinear.rank Z.base) b).asHom :=
      congrArg End.asHom
        ((congrArg (stageAction R (StableGeneralLinear.rank Z.base)) (fiber_comp R f g)).trans
          ((stageAction R (StableGeneralLinear.rank Z.base)).map_mul b
            (StableGeneralLinear.transition R _ _ h a)))
    change (stageSequence R).map (AsSmall.down.map (f.base ≫ g.base)) ≫
      (stageAction R (StableGeneralLinear.rank Z.base) (f ≫ g).fiber.down).asHom =
        ((stageSequence R).map (AsSmall.down.map f.base) ≫
          (stageAction R (StableGeneralLinear.rank Y.base) a).asHom) ≫
            (stageSequence R).map (AsSmall.down.map g.base) ≫
              (stageAction R (StableGeneralLinear.rank Z.base) b).asHom
    refine (congrArg (fun t => (stageSequence R).map
      (AsSmall.down.map (f.base ≫ g.base)) ≫ t) hc).trans ?_
    rw [(stageSequence R).map_comp (AsSmall.down.map f.base) (AsSmall.down.map g.base)]
    simpa only [Category.assoc] using congrArg
      (fun t => (stageSequence R).map (AsSmall.down.map f.base) ≫ t ≫
        (stageAction R (StableGeneralLinear.rank Z.base) b).asHom)
      (stageAction_transition R h a).symm

/-- On each original finite fiber the telescope functor is the original matrix action. -/
lemma inclusion_telescopeFunctor (n : ℕ) :
    CategoryTheory.Grothendieck.ι (StableGeneralLinear.categoryDiagram R)
        (StableGeneralLinear.rankIndex n) ⋙ telescopeFunctor R = stageFunctor R n := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  rcases X with ⟨⟨⟩⟩
  rcases Y with ⟨⟨⟩⟩
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  change (stageSequence R).map (𝟙 n) ≫
    (stageAction R n (@Mul.mul (Matrix.GeneralLinearGroup (Fin n) R) _ f.down 1)).asHom =
      (stageAction R n f.down).asHom
  exact (congrArg (fun t => t ≫ (stageAction R n
      (@Mul.mul (Matrix.GeneralLinearGroup (Fin n) R) _ f.down 1)).asHom)
      ((stageSequence R).map_id n)).trans
    ((Category.id_comp _).trans
      (congrArg (fun g ↦ (stageAction R n g).asHom)
        (mul_one (M := Matrix.GeneralLinearGroup (Fin n) R) _)))

/-- The rank-zero pair is exactly the two monoidal units, the zero base object. -/
lemma stageObject_zero : stageObject R 0 =
    (⟨𝟙_ (IsoCategory Rᵐᵒᵖ), 𝟙_ (IsoCategory Rᵐᵒᵖ)⟩ : Completion R) := rfl

end ModuleCat.FiniteProjective.StableCompletion
