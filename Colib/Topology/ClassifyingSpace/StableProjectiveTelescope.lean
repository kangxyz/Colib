/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.StableGeneralLinearMap
public import Colib.CategoryTheory.GroupCompletion.ProjectiveTelescope
public import Colib.CategoryTheory.Grothendieck.GroupoidRightFactors

/-!
Adapted from `Quillen/KTheory/Plus/StableProjectiveTelescope.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual objects,
functors, coefficient universes and comparison maps.

# Original finite matrix maps into the right projective telescope

The finite free object at rank `n` remains the chosen left-associated rank-one
power. The transition in the actual right-translation telescope uses the
specified braiding. Thus left and right tensoring are compared by actual
isomorphisms, never by an equality of their objects or functors.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Grothendieck
open scoped MonoidalLeftAction
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  ModuleCat.FiniteProjective.categoryDirectSumMonoidal
  ModuleCat.FiniteProjective.categoryDirectSumSymmetric
  ModuleCat.FiniteProjective.directSumMonoidal
  ModuleCat.FiniteProjective.directSumSymmetric

namespace ModuleCat.FiniteProjective.StableFreeRight
variable (R : Type u) [Ring R]

/-- The original finite free power, at its actual stage in the right telescope. -/
def stageObject (n : ℕ) : ProjectiveTelescope R :=
  ⟨n, AsSmall.up.obj (rankOnePower Rᵐᵒᵖ n)⟩

/-- The original finite matrix action, included at its actual telescope stage. -/
def stageAction (n : ℕ) : Matrix.GeneralLinearGroup (Fin n) R →* End (stageObject R n) :=
  ((AsSmall.up ⋙ Grothendieck.ι (projectiveTelescopeDiagram R) n).mapEnd _).comp
    (StableFree.powerEndEquiv R n).toMonoidHom

/-- The finite-stage action is exactly the original matrix endomorphism in the fiber. -/
lemma stageAction_eq (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (stageAction R n g).asHom = (Grothendieck.ι (projectiveTelescopeDiagram R) n).map
      (ULift.up ((StableFree.powerEndEquiv R n g).asHom)) := rfl

/-- The right successor functor, with the original arithmetic transport made explicit. -/
def stepFunctorIso (n : ℕ) :
    ((projectiveTelescopeDiagram R).map (homOfLE (Nat.le_succ n))).toFunctor ≅
      (AsSmall.down : AsSmall.{0} (IsoCategory Rᵐᵒᵖ) ⥤ IsoCategory Rᵐᵒᵖ) ⋙
        tensorRight (freeIso Rᵐᵒᵖ 1) ⋙ AsSmall.up :=
  Cat.Hom.toNatIso (eqToIso (TranslationTelescope.diagram_map_succ
    (freeIso Rᵐᵒᵖ 1) n))

/-- The actual fiber isomorphism aligning one right step with the chosen left power. -/
def stepIso (n : ℕ) :
    ((projectiveTelescopeDiagram R).map (homOfLE (Nat.le_succ n))).toFunctor.obj
      (AsSmall.up.obj (rankOnePower Rᵐᵒᵖ n)) ≅
        AsSmall.up.obj (rankOnePower Rᵐᵒᵖ (n + 1)) :=
  (stepFunctorIso R n).app _ ≪≫
    AsSmall.up.{u, u + 1, 0}.mapIso (β_ (rankOnePower Rᵐᵒᵖ n) (freeIso Rᵐᵒᵖ 1))

/-- Right addition is aligned with the chosen left power by the actual braiding. -/
def stageArrow (n : ℕ) : stageObject R n ⟶ stageObject R (n + 1) :=
  (Grothendieck.ιNatTrans (F := projectiveTelescopeDiagram R)
    (homOfLE (Nat.le_succ n))).app (AsSmall.up.obj (rankOnePower Rᵐᵒᵖ n)) ≫
      (Grothendieck.ι (projectiveTelescopeDiagram R) (n + 1)).map (stepIso R n).hom

/-- The original finite action commutes with the precise braiding in the right step. -/
lemma stepIso_naturality (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    ((projectiveTelescopeDiagram R).map (homOfLE (Nat.le_succ n))).toFunctor.map
        (AsSmall.up.{u, u + 1, 0}.map ((StableFree.powerEndEquiv R n g).asHom)) ≫ (stepIso R
          n).hom =
      (stepIso R n).hom ≫ AsSmall.up.{u, u + 1, 0}.map
        ((StableFree.powerEndEquiv R (n + 1) (StableGeneralLinear.step R n g)).asHom) := by
  have h :
      (AsSmall.down.{u, u + 1, 0} ⋙ tensorRight (freeIso Rᵐᵒᵖ 1) ⋙ AsSmall.up).map
          (AsSmall.up.{u, u + 1, 0}.map ((StableFree.powerEndEquiv R n g).asHom)) ≫
          AsSmall.up.{u, u + 1, 0}.map (β_ (rankOnePower Rᵐᵒᵖ n) (freeIso Rᵐᵒᵖ 1)).hom =
        AsSmall.up.{u, u + 1, 0}.map (β_ (rankOnePower Rᵐᵒᵖ n) (freeIso Rᵐᵒᵖ 1)).hom ≫
          AsSmall.up.{u, u + 1, 0}.map
            ((StableFree.powerEndEquiv R (n + 1) (StableGeneralLinear.step R n g)).asHom) := by
    apply ULift.ext
    change ((StableFree.powerEndEquiv R n g).asHom) ▷ freeIso Rᵐᵒᵖ 1 ≫ _ =
      _ ≫ (StableFree.powerEndEquiv R (n + 1) (StableGeneralLinear.step R n g)).asHom
    rw [StableFree.powerEndEquiv_step]
    exact BraidedCategory.braiding_naturality_left _ _
  simp only [stepIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
  erw [NatTrans.naturality_assoc, h]
  rfl


/-- The original matrix stabilization square commutes through the specified braiding. -/
lemma stageAction_step (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (stageAction R n g).asHom ≫ stageArrow R n =
      stageArrow R n ≫ (stageAction R (n + 1) (StableGeneralLinear.step R n g)).asHom := by
  rw [stageAction_eq, stageAction_eq]
  dsimp only [stageArrow]
  erw [← Category.assoc, NatTrans.naturality, Category.assoc]
  simp only [Functor.comp_map, Category.assoc]
  erw [← Functor.map_comp, ← Functor.map_comp, stepIso_naturality]
  rfl


/-- The sequence of actual braiding-aligned right telescope arrows. -/
abbrev stageSequence : ℕ ⥤ ProjectiveTelescope R where
  obj := stageObject R
  map {n m} f := Functor.OfSequence.map (stageArrow R) n m (leOfHom f)
  map_id n := Functor.OfSequence.map_id (stageArrow R) n
  map_comp f g :=
    Functor.OfSequence.map_comp (stageArrow R) _ _ _ (leOfHom f) (leOfHom g)

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
def stageFunctor (n : ℕ) : StableGeneralLinear.finiteCategory R n ⥤ ProjectiveTelescope R :=
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

/-- The original finite-stage maps define the right telescope bridge. -/
def telescopeFunctor :
    StableGeneralLinear.GrothendieckModel.Telescope R ⥤ ProjectiveTelescope R where
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
    (stageAction R n (@Mul.mul (Matrix.GeneralLinearGroup (Fin n) R) _ f.down 1)).asHom
      = (stageAction R n f.down).asHom
  exact (congrArg (fun t => t ≫ (stageAction R n
      (@Mul.mul (Matrix.GeneralLinearGroup (Fin n) R) _ f.down 1)).asHom)
        ((stageSequence R).map_id n)).trans
    ((Category.id_comp _).trans
      (congrArg (fun g ↦ (stageAction R n g).asHom)
        (mul_one (M := Matrix.GeneralLinearGroup (Fin n) R) _)))

/-- The distinguished matrix vertex maps to the original zero-stage projective vertex. -/
lemma telescopeFunctor_zero :
    (telescopeFunctor R).obj
      ⟨StableGeneralLinear.rankIndex 0, AsSmall.up.obj (SingleObj.star _)⟩ =
        projectiveTelescopeBase R := rfl

/-- The original identity-matrix stage chain in the finite matrix Grothendieck model. -/
def matrixSequence : ℕ ⥤ StableGeneralLinear.GrothendieckModel.Telescope R where
  obj n := ⟨StableGeneralLinear.rankIndex n, AsSmall.up.obj (SingleObj.star _)⟩
  map {n m} f :=
    { base := AsSmall.up.map f, fiber := ULift.up (1 : Matrix.GeneralLinearGroup (Fin m) R) }
  map_id n := by
    refine Grothendieck.ext _ _ rfl ?_
    simp only [eqToHom_refl, Category.id_comp]
    apply ULift.ext
    exact (fiber_id R
      ⟨StableGeneralLinear.rankIndex n, AsSmall.up.obj (SingleObj.star _)⟩).symm
  map_comp {n m k} f g := by
    refine Grothendieck.ext _ _ rfl ?_
    simp only [eqToHom_refl, Category.id_comp]
    apply ULift.ext
    change (1 : Matrix.GeneralLinearGroup (Fin k) R) =
      (1 * StableGeneralLinear.transition R m k (leOfHom g) 1) * 1
    simp

/-- Every matrix telescope object is one of the actual finite-stage vertices. -/
lemma exists_matrixSequence_obj (X : StableGeneralLinear.GrothendieckModel.Telescope R) :
    ∃ n, X = (matrixSequence R).obj n := by
  rcases X with ⟨⟨n⟩, ⟨⟨⟩⟩⟩
  exact ⟨n, rfl⟩

/-- The matrix identity chain is sent exactly to the braiding-aligned projective chain. -/
lemma matrixSequence_telescopeFunctor :
    matrixSequence R ⋙ telescopeFunctor R = stageSequence R := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro n m f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (stageSequence R).map f ≫ (stageAction R m 1).asHom = (stageSequence R).map f
  rw [map_one]
  exact Category.comp_id _

/-- The image of the original rank-n vertex stays at precisely stage n. -/
lemma telescopeFunctor_matrixSequence_base (n : ℕ) :
    ((telescopeFunctor R).obj ((matrixSequence R).obj n)).base = n := rfl

private instance stageInclusion_full (n : ℕ) :
    (Grothendieck.ι (projectiveTelescopeDiagram R) n).Full where
  map_surjective {X Y} f := by
    rcases f with ⟨b, f⟩
    have hb : b = 𝟙 n := Subsingleton.elim _ _
    subst b
    refine ⟨eqToHom (by simp) ≫ f, Grothendieck.ext _ _ rfl ?_⟩
    simp [Grothendieck.ι]

/-- Every finite-stage projective automorphism is an original finite matrix. -/
lemma stageAction_surjective (n : ℕ) : Function.Surjective (stageAction R n) := by
  intro f
  obtain ⟨g, hg⟩ := (Grothendieck.ι (projectiveTelescopeDiagram R) n).map_surjective f.asHom
  obtain ⟨a, ha⟩ := (StableFree.powerEndEquiv R n).surjective (End.of g.down)
  refine ⟨a, ?_⟩
  apply End.ext
  rw [stageAction_eq, ha]
  exact hg

/-- The actual finite matrix action is faithful. -/
lemma stageAction_injective (n : ℕ) : Function.Injective (stageAction R n) := by
  intro a b h
  have h := congrArg End.asHom h
  rw [stageAction_eq, stageAction_eq] at h
  have h' := (Grothendieck.ι (projectiveTelescopeDiagram R) n).map_injective h
  exact (StableFree.powerEndEquiv R n).injective (End.ext (congrArg ULift.down h'))

/-- Each actual telescope fiber remains the original projective isomorphism groupoid. -/
instance projectiveStage_isGroupoid (n : ℕ) :
    IsGroupoid ((projectiveTelescopeDiagram R).obj n) := by
  change IsGroupoid (AsSmall.{0} (IsoCategory Rᵐᵒᵖ))
  exact isGroupoid_of_reflects_iso (AsSmall.equiv (C := IsoCategory Rᵐᵒᵖ)).inverse

/-- The original finite-matrix bridge is faithful on all telescope arrows. -/
instance telescopeFunctor_faithful : (telescopeFunctor R).Faithful where
  map_injective {X Y} {f g} h := by
    cases f with | mk b f =>
      cases g with | mk c g =>
        obtain rfl : b = c := ULift.ext (Subsingleton.elim _ _)
        refine Grothendieck.ext (F := StableGeneralLinear.categoryDiagram R) _ _ rfl ?_
        simp only [eqToHom_refl, Category.id_comp]
        apply ULift.ext
        apply stageAction_injective R (StableGeneralLinear.rank Y.base)
        apply End.ext
        exact (cancel_epi ((stageSequence R).map (AsSmall.down.map b))).mp h

/-- Every arrow between the actual free stage objects comes from an original matrix arrow. -/
instance telescopeFunctor_full : (telescopeFunctor R).Full where
  map_surjective {X Y} f := by
    let h : StableGeneralLinear.rank X.base ≤ StableGeneralLinear.rank Y.base :=
      leOfHom f.base
    let s := (stageSequence R).map (homOfLE h)
    let q := Grothendieck.rightFactor (projectiveTelescopeDiagram R) s f (le_refl _)
    obtain ⟨g, hg⟩ := stageAction_surjective R (StableGeneralLinear.rank Y.base) (End.of q)
    refine ⟨{ base := AsSmall.up.map (homOfLE h), fiber := ULift.up g }, ?_⟩
    change s ≫ (stageAction R (StableGeneralLinear.rank Y.base) g).asHom = f
    rw [hg]
    exact Grothendieck.rightFactor_fac _ s f (le_refl _)

end ModuleCat.FiniteProjective.StableFreeRight
