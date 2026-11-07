/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Topology.ClassifyingSpace.ProjectiveCompletionRetraction
public import Colib.CategoryTheory.GroupCompletion.TelescopeUnit
public import Colib.CategoryTheory.Grothendieck.EndofunctorTelescopeCoconeNaturality

/-!
Adapted from `Quillen/KTheory/Plus/ProjectiveCompletionUnit.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`; original functors and arrows retained.

# The original telescope unit and the original completion map -/
@[expose] public section

open CategoryTheory.GroupCompletion

noncomputable section
open CategoryTheory MonoidalCategory Grothendieck
universe u
namespace ModuleCat.FiniteProjective.StableFreeRight
open GroupCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal directSumSymmetric
variable (R : Type u) [Ring R]

/-- The actual completed-diagram identification is the identity on each original fiber. -/
theorem completedDiagramIdentification_app (n : ℕ) :
    (eqToHom (projectiveCompletedTelescopeDiagram_eq R)).app n =
      𝟙 (Cat.of (StableCompletion.Completion R)) := by
  rw [eqToHom_app]
  rfl

/-- The completed-diagram identification with computationally original identity fibers. -/
def completedDiagramIdentification : projectiveCompletedTelescopeDiagram R ⟶
    EndofunctorTelescope.diagram (Localization.secondTranslation (freeIso Rᵐᵒᵖ 1)) where
  app _ := 𝟙 (Cat.of (StableCompletion.Completion R))
  naturality {n m} h := by
    have hh := (eqToHom (projectiveCompletedTelescopeDiagram_eq R)).naturality h
    simpa only [completedDiagramIdentification_app] using hh

/-- Exposing identity fibers does not change the original diagram identification. -/
theorem completedDiagramIdentification_eq :
    completedDiagramIdentification R = eqToHom (projectiveCompletedTelescopeDiagram_eq R) := by
  apply NatTrans.ext
  funext n
  exact (completedDiagramIdentification_app R n).symm

/-- The actual unit lift into the original completed endofunctor telescope. -/
def originalUnitLift : EndofunctorTelescope.Model (tensorRight (freeIso Rᵐᵒᵖ 1)) ⥤
    EndofunctorTelescope.Model (Localization.secondTranslation (freeIso Rᵐᵒᵖ 1)) :=
  TranslationTelescope.originalTelescopeUnit (freeIso Rᵐᵒᵖ 1) ⋙
    Grothendieck.map (completedDiagramIdentification R)

/-- The unit lift sends the genuine successor to the genuine completed successor. -/
theorem originalUnitLift_successor (n : ℕ) {X Y : IsoCategory Rᵐᵒᵖ}
    (f : X ⊗ freeIso Rᵐᵒᵖ 1 ⟶ Y) :
    HEq ((originalUnitLift R).map
      (EndofunctorTelescope.successorArrow (tensorRight (freeIso Rᵐᵒᵖ 1)) n f))
      (EndofunctorTelescope.successorArrow (Localization.secondTranslation (freeIso Rᵐᵒᵖ 1)) n
        (X := (Localization.unitEntry (C := IsoCategory Rᵐᵒᵖ)).obj X)
        (Y := (Localization.unitEntry (C := IsoCategory Rᵐᵒᵖ)).obj Y)
        ((Localization.unitEntry (C := IsoCategory Rᵐᵒᵖ) (D := IsoCategory Rᵐᵒᵖ)).map f)) := by
  apply heq_of_eq
  refine Grothendieck.ext _ _ rfl ?_
  simp only [eqToHom_refl, Category.id_comp]
  dsimp only [originalUnitLift, Functor.comp_map, Grothendieck.map,
    completedDiagramIdentification, TranslationTelescope.originalTelescopeUnit,
    EndofunctorTelescope.successorArrow]
  simp only [Functor.map_comp, eqToHom_map, Cat.eqToHom_app, Cat.Hom.id_toFunctor,
    Functor.id_map, eqToHom_trans_assoc]


/-- The explicit diagram identification retains each original completed inclusion. -/
theorem completedDiagramIdentification_stage (n : ℕ) :
    Grothendieck.ι (projectiveCompletedTelescopeDiagram R) n ⋙
      Grothendieck.map (completedDiagramIdentification R) =
    Grothendieck.ι (EndofunctorTelescope.diagram
      (Localization.secondTranslation (freeIso Rᵐᵒᵖ 1))) n := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  have h := (Grothendieck.ιCompMap (completedDiagramIdentification R) n).hom.naturality f
  simp only [Grothendieck.ιCompMap, NatIso.ofComponents_hom_app, Iso.refl_hom,
    Category.id_comp, Category.comp_id] at h
  exact h

/-- The original unit is retained in every completed fiber. -/
theorem originalUnitLift_stage (n : ℕ) :
    Grothendieck.ι (EndofunctorTelescope.diagram (tensorRight (freeIso Rᵐᵒᵖ 1))) n ⋙
      originalUnitLift R =
    Localization.unitEntry ⋙ Grothendieck.ι (EndofunctorTelescope.diagram
      (Localization.secondTranslation (freeIso Rᵐᵒᵖ 1))) n := by
  rw [originalUnitLift, ← Functor.assoc, TranslationTelescope.originalTelescopeUnit_stage,
    Functor.assoc]
  erw [completedDiagramIdentification_stage]

/-- Apply the original inverse completed cocone to the original lifted unit. -/
def originalUnitRetraction := originalUnitLift R ⋙ originalCompletedRetraction R

/-- Restriction of the actual composite to each original fiber. -/
theorem originalUnitRetraction_stage (n : ℕ) :
    Grothendieck.ι (EndofunctorTelescope.diagram (tensorRight (freeIso Rᵐᵒᵖ 1))) n ⋙
      originalUnitRetraction R = Localization.unitEntry ⋙ completedInverseFiber R n := by
  rw [originalUnitRetraction, ← Functor.assoc, originalUnitLift_stage, Functor.assoc,
    originalCompletedRetraction, EndofunctorTelescope.inclusion_functorFromSequence]

/-- The original left-unitor comparison on an actual telescope fiber. -/
def originalUnitRetractionStageHom (n : ℕ) :
    Grothendieck.ι (EndofunctorTelescope.diagram (tensorRight (freeIso Rᵐᵒᵖ 1))) n ⋙
      originalUnitRetraction R ⟶
    Grothendieck.ι (EndofunctorTelescope.diagram (tensorRight (freeIso Rᵐᵒᵖ 1))) n ⋙
      originalCompletionFunctor R :=
  eqToHom (originalUnitRetraction_stage R n) ≫ completedInverseFiberUnitHom R n ≫
    eqToHom (EndofunctorTelescope.inclusion_functorFromSequence _
      (completionFiber R) (completionStep R) n).symm

/-- The stage comparison retains the literal specified left-unitor arrow. -/
theorem originalUnitRetractionStageHom_app (n : ℕ) (X : IsoCategory Rᵐᵒᵖ) :
    (originalUnitRetractionStageHom R n).app X =
      (completedInverseFiberUnitHom R n).app X := by
  simp only [originalUnitRetractionStageHom, NatTrans.comp_app, eqToHom_app,
    eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The composite retains the original inverse-cocone successor formula. -/
theorem originalUnitRetraction_successor (n : ℕ) {X Y : IsoCategory Rᵐᵒᵖ}
    (f : X ⊗ freeIso Rᵐᵒᵖ 1 ⟶ Y) :
    (originalUnitRetraction R).map
      (EndofunctorTelescope.successorArrow (tensorRight (freeIso Rᵐᵒᵖ 1)) n f) =
    (completedInverseStep R n).app (Localization.unitEntry.obj X) ≫
      (completedInverseFiber R (n + 1)).map
        ((Localization.unitEntry (C := IsoCategory Rᵐᵒᵖ)).map f) := by
  dsimp only [originalUnitRetraction, Functor.comp_map]
  rw [eq_of_heq (originalUnitLift_successor R n f)]
  exact EndofunctorTelescope.functorFromSequence_map_successor _ _ _ n _

/-- The actual stage comparison respects every prescribed successor arrow. -/
theorem originalUnitRetractionStageHom_successor (n : ℕ) {X Y : IsoCategory Rᵐᵒᵖ}
    (f : X ⊗ freeIso Rᵐᵒᵖ 1 ⟶ Y) :
    (originalUnitRetraction R).map
        (EndofunctorTelescope.successorArrow (tensorRight (freeIso Rᵐᵒᵖ 1)) n f) ≫
      (originalUnitRetractionStageHom R (n + 1)).app Y =
    (originalUnitRetractionStageHom R n).app X ≫
      (originalCompletionFunctor R).map
        (EndofunctorTelescope.successorArrow (tensorRight (freeIso Rᵐᵒᵖ 1)) n f) := by
  rw [originalUnitRetraction_successor, originalUnitRetractionStageHom_app,
    originalUnitRetractionStageHom_app]
  dsimp only [originalCompletionFunctor]
  erw [EndofunctorTelescope.functorFromSequence_map_successor]
  erw [Category.assoc, (completedInverseFiberUnitHom R (n + 1)).naturality f,
    ← Category.assoc, completedInverseFiberUnit_successor, Category.assoc]

/-- The original stage transformations satisfy the canonical Grothendieck successor square. -/
theorem originalUnitRetractionStageHom_transition (n : ℕ)
    (X : IsoCategory Rᵐᵒᵖ) :
    (originalUnitRetraction R).map
        ((Grothendieck.ιNatTrans (F := EndofunctorTelescope.diagram
          (tensorRight (freeIso Rᵐᵒᵖ 1))) (homOfLE (Nat.le_succ n))).app X) ≫
      (originalUnitRetractionStageHom R (n + 1)).app
        (((EndofunctorTelescope.diagram (tensorRight (freeIso Rᵐᵒᵖ 1))).map
          (homOfLE (Nat.le_succ n))).toFunctor.obj X) =
    (originalUnitRetractionStageHom R n).app X ≫
      (originalCompletionFunctor R).map
        ((Grothendieck.ιNatTrans (F := EndofunctorTelescope.diagram
          (tensorRight (freeIso Rᵐᵒᵖ 1))) (homOfLE (Nat.le_succ n))).app X) := by
  let f : X ⊗ freeIso Rᵐᵒᵖ 1 ⟶
      (((EndofunctorTelescope.diagram (tensorRight (freeIso Rᵐᵒᵖ 1))).map
        (homOfLE (Nat.le_succ n))).toFunctor.obj X) := eqToHom (by
    change _ = (EndofunctorTelescope.iterate (tensorRight (freeIso Rᵐᵒᵖ 1)) (n + 1 - n)).obj X
    rw [Nat.add_sub_cancel_left]
    rfl)
  have hf : (EndofunctorTelescope.successorArrow (tensorRight (freeIso Rᵐᵒᵖ 1)) n f) =
      ((Grothendieck.ιNatTrans (F := EndofunctorTelescope.diagram
        (tensorRight (freeIso Rᵐᵒᵖ 1))) (homOfLE (Nat.le_succ n))).app X) := by
    refine Grothendieck.ext _ _ rfl ?_
    simp only [eqToHom_refl, Category.id_comp]
    change eqToHom _ ≫ eqToHom _ = 𝟙 _
    simp only [eqToHom_trans, eqToHom_refl]
  rw [← hf]
  exact originalUnitRetractionStageHom_successor R n f

/-- The prescribed original unit corrections extend over the actual infinite telescope. -/
def originalUnitCompletionHom : originalUnitRetraction R ⟶ originalCompletionFunctor R :=
  Grothendieck.Sequence.natTransFromSuccessors _ _ _ (originalUnitRetractionStageHom R)
    (originalUnitRetractionStageHom_transition R)

/-- Exposing identity fibers has retained the original completed cocone composite exactly. -/
theorem originalUnitRetraction_eq : originalUnitRetraction R =
    TranslationTelescope.originalTelescopeUnit (freeIso Rᵐᵒᵖ 1) ⋙ completedRetraction R := by
  dsimp only [originalUnitRetraction, originalUnitLift, completedRetraction]
  rw [completedDiagramIdentification_eq]
  rfl

/-- The lifted original unit has the exact composite used by the infinite correction. -/
theorem telescopeUnitRetraction_eq :
    TranslationTelescope.telescopeUnit (freeIso Rᵐᵒᵖ 1) ⋙ completedRetraction R =
    (TranslationTelescope.modelEquivalence (freeIso Rᵐᵒᵖ 1)).functor ⋙
      originalUnitRetraction R := by
  rw [originalUnitRetraction_eq]
  rfl

/-- The original precompletion unit followed by the actual completed retraction
is naturally transformed to the original stable-completion functor. -/
def telescopeUnitCompletionHom :
    TranslationTelescope.telescopeUnit (freeIso Rᵐᵒᵖ 1) ⋙ completedRetraction R ⟶
      completionFunctor R :=
  eqToHom (telescopeUnitRetraction_eq R) ≫
    Functor.whiskerLeft (TranslationTelescope.modelEquivalence (freeIso Rᵐᵒᵖ 1)).functor
      (originalUnitCompletionHom R)

/-- Every original stage retains precisely its left-unitor correction and the
specified diagram-identification transport. -/
theorem telescopeUnitCompletionHom_app (n : ℕ) (X : IsoCategory Rᵐᵒᵖ) :
    (telescopeUnitCompletionHom R).app ⟨n, AsSmall.up.obj X⟩ =
      eqToHom (congrArg (fun F ↦ F.obj ⟨n, AsSmall.up.obj X⟩)
        (telescopeUnitRetraction_eq R)) ≫
      (completedInverseFiberUnitHom R n).app X := by
  simp only [telescopeUnitCompletionHom, NatTrans.comp_app, eqToHom_app,
    Functor.whiskerLeft_app]
  change eqToHom _ ≫ (originalUnitRetractionStageHom R n).app X = _
  rw [originalUnitRetractionStageHom_app]

end ModuleCat.FiniteProjective.StableFreeRight
