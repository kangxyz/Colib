/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.ProjectiveTelescopeComma
public import Colib.CategoryTheory.GroupCompletion.TelescopeInterchangeEquivalence
public import Colib.CategoryTheory.GroupCompletion.StableGeneralLinearMap
public import Colib.Topology.ClassifyingSpace.UniverseHomotopy

/-! # Original completed projective telescope and localization interchange

This identifies localization of the precompletion telescope with the telescope
of the completed category. It does not identify the precompletion telescope
itself with the completed category.
-/

/-!
Implementation provenance: adapted from
`Quillen/KTheory/Plus/ProjectiveTelescopeInterchange.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original functors,
comparison maps, homotopies, hypotheses and universes are retained.
-/

@[expose] public section

open CategoryTheory.GroupCompletion

noncomputable section
open CategoryTheory MonoidalCategory Grothendieck
universe u
namespace ModuleCat.FiniteProjective
open GroupCompletion
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal projectiveTelescopeAction
variable (R : Type u) [Ring R]

/-- The completed sequence, with the original second-coordinate right-free stabilization. -/
def projectiveCompletedTelescopeDiagram : ℕ ⥤ Cat.{u + 1, u + 1} :=
  TranslationTelescope.localizationDiagram (freeIso Rᵐᵒᵖ 1)

/-- The sequence is literally the original completed translation diagram. -/
theorem projectiveCompletedTelescopeDiagram_eq :
    projectiveCompletedTelescopeDiagram R =
      EndofunctorTelescope.diagram (Localization.secondTranslation (freeIso Rᵐᵒᵖ 1)) :=
  TranslationTelescope.localizationDiagram_eq _

/-- Each actual completed stage enters localization of the original telescope. -/
def projectiveCompletionStage (n : ℕ) :
    StableCompletion.Completion R ⥤ ProjectiveTelescopeLocalization R :=
  TranslationTelescope.localizationStage (freeIso Rᵐᵒᵖ 1) n

/-- The actual equivalence retains the completed stage cocone and original quotient maps. -/
def projectiveTelescopeInterchange :
    Grothendieck (projectiveCompletedTelescopeDiagram R) ≌ ProjectiveTelescopeLocalization R :=
  TranslationTelescope.localizationInterchangeEquivalence (freeIso Rᵐᵒᵖ 1)

/-- Its forward functor restricts to the original map at every stage. -/
theorem projectiveTelescopeInterchange_stage (n : ℕ) :
    Grothendieck.ι (projectiveCompletedTelescopeDiagram R) n ⋙
        (projectiveTelescopeInterchange R).functor = projectiveCompletionStage R n :=
  TranslationTelescope.localizationInterchange_stage _ n

/-- The original stage inclusion and original localization unit form an exact square. -/
theorem projectiveCompletionStage_unit (n : ℕ) :
    Localization.unitEntry (C := IsoCategory Rᵐᵒᵖ) (D := IsoCategory Rᵐᵒᵖ) ⋙
        projectiveCompletionStage R n =
      TranslationTelescope.stageInclusion (freeIso Rᵐᵒᵖ 1) n ⋙
        Localization.unitEntry (C := IsoCategory Rᵐᵒᵖ) (D := ProjectiveTelescope R) :=
  TranslationTelescope.localizationStage_unitEntry _ n

/-- Realization gives a genuine homotopy equivalence of these precise two models. -/
def projectiveTelescopeInterchangeHomotopyEquiv :
    ContinuousMap.HomotopyEquiv
      (ClassifyingSpace (Grothendieck (projectiveCompletedTelescopeDiagram R)))
      (ClassifyingSpace (ProjectiveTelescopeLocalization R)) :=
  equivalenceClassifyingHomotopyEquivUniversal (projectiveTelescopeInterchange R)

/-- The forward continuous map is the realization of the original interchange functor. -/
theorem projectiveTelescopeInterchangeHomotopyEquiv_toFun :
    (projectiveTelescopeInterchangeHomotopyEquiv R).toFun =
      classifyingSpaceMapUniversal (projectiveTelescopeInterchange R).functor := rfl

end ModuleCat.FiniteProjective
