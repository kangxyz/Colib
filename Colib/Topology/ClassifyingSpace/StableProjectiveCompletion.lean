/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.StableGeneralLinearMap
public import Colib.CategoryTheory.GroupCompletion.ProjectiveTelescope
public import Colib.CategoryTheory.GroupCompletion.UnitEntry
public import Colib.CategoryTheory.Grothendieck.EndofunctorTelescopeCocone
public import Colib.Topology.ClassifyingSpace.StableProjectiveTelescope
public import Colib.Topology.ClassifyingSpace.StableGeneralLinearCompletion

/-!
Adapted from `Quillen/KTheory/Plus/StableProjectiveCompletion.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual objects,
functors, coefficient universes and comparison maps.

# The original completion map from the right-projective telescope

The denominator at stage n is the original rank-one power. A specified braiding
aligns right projective translation with left common-denominator translation.
This gives a strict square with the original finite-matrix telescope functor,
including its prescribed stable map into the genuine zero path component.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Grothendieck
open scoped MonoidalLeftAction
attribute [local instance] ModuleCat.FiniteProjective.categoryDirectSumMonoidal
  ModuleCat.FiniteProjective.directSumMonoidal
  ModuleCat.FiniteProjective.directSumSymmetric
namespace ModuleCat.FiniteProjective.StableFreeRight
variable (R : Type u) [Ring R]

/-- The stage-n completion functor with the original power denominator. -/
def completionFiber (n : ℕ) : IsoCategory Rᵐᵒᵖ ⥤ StableCompletion.Completion R where
  obj P := ⟨rankOnePower Rᵐᵒᵖ n, P⟩
  map f := GroupCompletion.ActionLocalization.ofHom (𝟙 _, f)
  map_id P := GroupCompletion.ActionLocalization.ofHom_id _
  map_comp {P Q S} f g := by
    simpa using GroupCompletion.ActionLocalization.ofHom_comp
      (C := IsoCategory Rᵐᵒᵖ)
      (X := (rankOnePower Rᵐᵒᵖ n, P)) (Y := (rankOnePower Rᵐᵒᵖ n, Q))
      (Z := (rankOnePower Rᵐᵒᵖ n, S)) (𝟙 _, f) (𝟙 _, g)

/-- The actual right-tensor successor, transported by the specified braiding. -/
def completionStep (n : ℕ) :
    completionFiber R n ⟶ tensorRight (freeIso Rᵐᵒᵖ 1) ⋙ completionFiber R (n + 1) where
  app P := GroupCompletion.ActionLocalization.translation (freeIso Rᵐᵒᵖ 1)
      (rankOnePower Rᵐᵒᵖ n, P) ≫
    GroupCompletion.ActionLocalization.ofHom (𝟙 _, (β_ (freeIso Rᵐᵒᵖ 1) P).hom)
  naturality P Q f := by
    dsimp [completionFiber]
    rw [← Category.assoc, GroupCompletion.ActionLocalization.ofHom_translation,
      Category.assoc, ← GroupCompletion.ActionLocalization.ofHom_comp,
      Category.assoc, ← GroupCompletion.ActionLocalization.ofHom_comp]
    congr 1
    apply congrArg GroupCompletion.ActionLocalization.ofHom
    apply Prod.ext
    · change freeIso Rᵐᵒᵖ 1 ◁ 𝟙 (rankOnePower Rᵐᵒᵖ n) ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
      simp
    · exact BraidedCategory.braiding_naturality_right _ _

/-- Each matrix fiber is exactly the original finite completion functor. -/
lemma completionFiber_powerFunctor (n : ℕ) :
    AsSmall.down ⋙ StableFree.powerFunctor R n ⋙ completionFiber R n =
      StableCompletion.stageFunctor R n := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y g
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- The specified successor braiding cancels against the bridge braiding. -/
lemma completionStep_braiding (n : ℕ) :
    (completionStep R n).app (rankOnePower Rᵐᵒᵖ n) ≫
      (completionFiber R (n + 1)).map
        (β_ (rankOnePower Rᵐᵒᵖ n) (freeIso Rᵐᵒᵖ 1)).hom =
      StableCompletion.stageArrow R n := by
  dsimp [completionStep, completionFiber, StableCompletion.stageArrow]
  rw [Category.assoc, ← GroupCompletion.ActionLocalization.ofHom_comp]
  simp only [prod_comp, selfLeftAction_actionObj, SymmetricCategory.symmetry]
  erw [Category.id_comp, GroupCompletion.ActionLocalization.ofHom_id, Category.comp_id]

/-- At stage zero this is exactly the original unit-entry functor. -/
lemma completionFiber_zero : completionFiber R 0 = GroupCompletion.Localization.unitEntry := rfl

/-- The prescribed lax cocone extended over the actual right-endofunctor telescope. -/
def originalCompletionFunctor :
    EndofunctorTelescope.Model (tensorRight (freeIso Rᵐᵒᵖ 1)) ⥤ StableCompletion.Completion R :=
  EndofunctorTelescope.functorFromSequence _ (completionFiber R) (completionStep R)

/-- The original right-projective telescope map to the projective completion category. -/
def completionFunctor : ProjectiveTelescope R ⥤ StableCompletion.Completion R :=
  (TranslationTelescope.modelEquivalence (freeIso Rᵐᵒᵖ 1)).functor ⋙ originalCompletionFunctor R

/-- Completion records the original numerator and the actual rank-one-power denominator. -/
lemma completionFunctor_obj (n : ℕ) (P : IsoCategory Rᵐᵒᵖ) :
    (completionFunctor R).obj ⟨n, AsSmall.up.obj P⟩ =
      (⟨rankOnePower Rᵐᵒᵖ n, P⟩ : StableCompletion.Completion R) := rfl

/-- Completion retains the prescribed functor on every original projective fiber. -/
lemma completionFunctor_inclusion (n : ℕ) :
    Grothendieck.ι (projectiveTelescopeDiagram R) n ⋙ completionFunctor R =
      AsSmall.down ⋙ completionFiber R n := by
  change (Grothendieck.ι (TranslationTelescope.diagram (freeIso Rᵐᵒᵖ 1)) n ⋙
    (TranslationTelescope.modelEquivalence (freeIso Rᵐᵒᵖ 1)).functor) ⋙
      originalCompletionFunctor R = _
  rw [TranslationTelescope.inclusion_forward, Functor.assoc, originalCompletionFunctor,
    EndofunctorTelescope.inclusion_functorFromSequence]

/-- The original zero-stage inclusion retains exactly the original unit-entry map. -/
lemma completionFunctor_zero_inclusion :
    Grothendieck.ι (projectiveTelescopeDiagram R) 0 ⋙ completionFunctor R =
      AsSmall.down ⋙ GroupCompletion.Localization.unitEntry
        (C := IsoCategory Rᵐᵒᵖ) (D := IsoCategory Rᵐᵒᵖ) := by
  rw [completionFunctor_inclusion, completionFiber_zero]

/-- Every original matrix action is retained exactly. -/
lemma completionFunctor_stageAction (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (completionFunctor R).map ((stageAction R n g).asHom) = (StableCompletion.stageAction R n
      g).asHom := by
  rw [stageAction_eq]
  change (Grothendieck.ι (projectiveTelescopeDiagram R) n ⋙ completionFunctor R).map
      (ULift.up ((StableFree.powerEndEquiv R n g).asHom)) =
    (AsSmall.down ⋙ completionFiber R n).map (ULift.up ((StableFree.powerEndEquiv R n g).asHom))
  have h := Functor.congr_hom (completionFunctor_inclusion R n)
    (ULift.up ((StableFree.powerEndEquiv R n g).asHom))
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h

/-- The prescribed right-telescope basepoint maps exactly to the zero pair. -/
lemma completionFunctor_base : (completionFunctor R).obj (projectiveTelescopeBase R) =
    StableCompletion.stageObject R 0 := rfl

/-- The actual projective successor becomes the prescribed braided endofunctor successor. -/
lemma stageArrow_forward (n : ℕ) :
    (TranslationTelescope.modelEquivalence (freeIso Rᵐᵒᵖ 1)).functor.map (stageArrow R n) =
      EndofunctorTelescope.successorArrow (tensorRight (freeIso Rᵐᵒᵖ 1)) n
        (β_ (rankOnePower Rᵐᵒᵖ n) (freeIso Rᵐᵒᵖ 1)).hom := by
  refine Grothendieck.ext _ _ (Subsingleton.elim _ _) ?_
  simp only [EndofunctorTelescope.diagram, TranslationTelescope.modelEquivalence,
    Grothendieck.compAsSmallFunctorEquivalence, Grothendieck.compAsSmallFunctorEquivalenceFunctor,
    Cat.of_α, AsSmall.down_obj, Functor.toCatHom_toFunctor, AsSmall.down_map, stageObject,
    projectiveTelescopeDiagram, TranslationTelescope.diagram, AsSmall.up_obj_down,
    EndofunctorTelescope.successorArrow, homOfLE_leOfHom, Functor.flip_obj_obj,
    curriedTensor_obj_obj, stageArrow, Functor.comp_obj, Cat.asSmallFunctor_obj,
    Nat.succ_eq_add_one, Functor.comp_map, Cat.asSmallFunctor_map, Grothendieck.ι,
    Grothendieck.ιNatTrans, stepIso, stepFunctorIso, Functor.flip_obj_map,
    curriedTensor_map_app, Cat.Hom.toNatIso, eqToIso.hom, eqToIso.inv, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom, Grothendieck.comp_base, Grothendieck.comp_fiber,
    down_comp, AsSmall.up_map_down, eqToHom_refl, eqToHom_down,
    Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app, eqToHom_trans_assoc, add_tsub_cancel_left,
    EndofunctorTelescope.iterate_succ, EndofunctorTelescope.iterate, Functor.id_obj,
    tsub_self, EndofunctorTelescope.iterate_zero, eqToHom_naturality_assoc, Category.id_comp]
  change eqToHom _ ≫ (EndofunctorTelescope.iterate (tensorRight (freeIso Rᵐᵒᵖ 1))
    (n + 1 - (n + 1))).map (𝟙 _) ≫ eqToHom _ ≫ _ = eqToHom _ ≫ _
  simp

/-- The right-translation successor becomes exactly the original diagonal translation. -/
lemma completionFunctor_stageArrow (n : ℕ) :
    (completionFunctor R).map (stageArrow R n) = StableCompletion.stageArrow R n := by
  change (originalCompletionFunctor R).map
    ((TranslationTelescope.modelEquivalence (freeIso Rᵐᵒᵖ 1)).functor.map (stageArrow R n)) = _
  rw [stageArrow_forward]
  exact (EndofunctorTelescope.functorFromSequence_map_successor _
    (completionFiber R) (completionStep R) n _).trans (completionStep_braiding R n)

/-- Every original finite-rank transition is retained by completion. -/
lemma completionFunctor_stageSequence {n m : ℕ} (h : n ≤ m) :
    (completionFunctor R).map ((stageSequence R).map (homOfLE h)) =
      (StableCompletion.stageSequence R).map (homOfLE h) := by
  induction h using Nat.leRec with
  | refl =>
    change (completionFunctor R).map ((stageSequence R).map (𝟙 n)) =
      (StableCompletion.stageSequence R).map (𝟙 n)
    rw [(stageSequence R).map_id n, (completionFunctor R).map_id,
      (StableCompletion.stageSequence R).map_id n]
    rfl
  | @le_succ_of_le m h ih =>
    rw [← homOfLE_comp h (Nat.le_succ m), Functor.map_comp, Functor.map_comp,
      Functor.map_comp, ih]
    rw [show (stageSequence R).map (homOfLE (Nat.le_succ m)) = stageArrow R m from
      Functor.ofSequence_map_homOfLE_succ _ m]
    rw [show (StableCompletion.stageSequence R).map (homOfLE (Nat.le_succ m)) =
      StableCompletion.stageArrow R m from Functor.ofSequence_map_homOfLE_succ _ m]
    rw [completionFunctor_stageArrow]

/-- The actual matrix-to-projective bridge commutes strictly with the original completion map. -/
lemma telescopeFunctor_completionFunctor :
    telescopeFunctor R ⋙ completionFunctor R = StableCompletion.telescopeFunctor R := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (completionFunctor R).map
      ((stageSequence R).map (AsSmall.down.map f.base) ≫
        (stageAction R (StableGeneralLinear.rank Y.base) f.fiber.down).asHom) = _
  rw [Functor.map_comp, completionFunctor_stageAction]
  exact congrArg (fun q => q ≫ (StableCompletion.stageAction R
      (StableGeneralLinear.rank Y.base) f.fiber.down).asHom)
    (completionFunctor_stageSequence R (leOfHom (AsSmall.down.map f.base)))

/-- Realization preserves the exact original matrix-to-completion square. -/
lemma telescopeMap_completionMap :
    (classifyingSpaceMapUniversal (completionFunctor R)).comp
      (classifyingSpaceMapUniversal (telescopeFunctor R)) =
        StableCompletion.telescopeMap R := by
  rw [← classifyingSpaceMapUniversal_comp, telescopeFunctor_completionFunctor]
  rfl

/-- The fixed inverse of the original stable projection gives the original stable map. -/
lemma stableMap_completionMap :
    (classifyingSpaceMapUniversal (completionFunctor R)).comp
      ((classifyingSpaceMapUniversal (telescopeFunctor R)).comp
        (StableCompletion.originalStableToTelescope R)) =
      StableCompletion.stableMap R := by
  rw [← ContinuousMap.comp_assoc, telescopeMap_completionMap]
  rfl

/-- The completion of the original stable projective map has exactly the prescribed
value in the genuine zero path component. -/
lemma stableZeroMap_completionMap_val
    (x : ClassifyingSpace (SingleObj (StableGeneralLinear.Group R))) :
    classifyingSpaceMapUniversal (completionFunctor R)
      (classifyingSpaceMapUniversal (telescopeFunctor R)
        (StableCompletion.originalStableToTelescope R x)) =
      (StableCompletion.stableZeroMap R x).val := by
  exact congrArg (fun f => f x) (stableMap_completionMap R)

end ModuleCat.FiniteProjective.StableFreeRight
