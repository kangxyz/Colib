/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.ProjectiveTelescopeComponents
public import Colib.CategoryTheory.Monoidal.RightIterationTracks

/-!
Adapted from `Quillen/KTheory/Plus/ProjectiveStageComponents.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original projective
complements, stage maps and coefficient transports are retained.
 # Component reflection for actual finite-stage translations -/

@[expose] public section
noncomputable section
open CategoryTheory MonoidalCategory Grothendieck
universe u
namespace ModuleCat.FiniteProjective
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal directSumSymmetric
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable (R : Type u) [Ring R]

/-- The original common-universe stage category. -/
abbrev ProjectiveStage := AsSmall.{0} (IsoCategory Rᵐᵒᵖ)

/-- Actual left addition at a finite stage. -/
def projectiveStageLeft (P : IsoCategory Rᵐᵒᵖ) : ProjectiveStage R ⥤ ProjectiveStage R :=
  AsSmall.down ⋙ tensorLeft P ⋙ AsSmall.up

/-- Actual right addition at a finite stage. -/
def projectiveStageRight (Q : IsoCategory Rᵐᵒᵖ) : ProjectiveStage R ⥤ ProjectiveStage R :=
  AsSmall.down ⋙ tensorRight Q ⋙ AsSmall.up

/-- The finite-stage braiding retains the original module isomorphism. -/
def projectiveStageRightLeftIso (P : IsoCategory Rᵐᵒᵖ) :
    projectiveStageRight R P ≅ projectiveStageLeft R P :=
  Functor.isoWhiskerLeft AsSmall.down
    (Functor.isoWhiskerRight (TranslationTelescope.rightLeftBraidingIso P) AsSmall.up)

/-- The original stage square holds for actual realized points. -/
theorem projectiveStageLeft_infinite (P : IsoCategory Rᵐᵒᵖ) (n : ℕ)
    (x : ClassifyingSpace (ProjectiveStage R)) :
    classifyingSpaceMap (Grothendieck.ι (projectiveTelescopeDiagram R) n)
        (classifyingSpaceMap (projectiveStageLeft R P) x) =
      classifyingSpaceMap (projectiveTelescopeTranslation R P)
        (classifyingSpaceMap (Grothendieck.ι (projectiveTelescopeDiagram R) n) x) := by
  change (classifyingSpaceMap (projectiveStageLeft R P) ≫
    classifyingSpaceMap (Grothendieck.ι (projectiveTelescopeDiagram R) n)) x =
    (classifyingSpaceMap (Grothendieck.ι (projectiveTelescopeDiagram R) n) ≫
      classifyingSpaceMap (projectiveTelescopeTranslation R P)) x
  rw [← classifyingSpaceMap_comp, ← classifyingSpaceMap_comp,
    projectiveTelescopeTranslation_stage]
  rfl

/-- Original left addition preserves and reflects components after stage inclusion. -/
theorem projectiveStageLeft_infinite_joined_iff (P : IsoCategory Rᵐᵒᵖ) (n : ℕ)
    (x y : ClassifyingSpace (ProjectiveStage R)) :
    Joined (classifyingSpaceMap (Grothendieck.ι (projectiveTelescopeDiagram R) n)
        (classifyingSpaceMap (projectiveStageLeft R P) x))
      (classifyingSpaceMap (Grothendieck.ι (projectiveTelescopeDiagram R) n)
        (classifyingSpaceMap (projectiveStageLeft R P) y)) ↔
    Joined (classifyingSpaceMap (Grothendieck.ι (projectiveTelescopeDiagram R) n) x)
      (classifyingSpaceMap (Grothendieck.ι (projectiveTelescopeDiagram R) n) y) := by
  rw [projectiveStageLeft_infinite, projectiveStageLeft_infinite]
  exact projectiveTelescopeTranslation_joined_iff R P _ _

/-- Finite-stage right addition has the same reflection property through its actual braiding. -/
theorem projectiveStageRight_infinite_joined_iff (P : IsoCategory Rᵐᵒᵖ) (n : ℕ)
    (x y : ClassifyingSpace (ProjectiveStage R)) :
    Joined (classifyingSpaceMap (Grothendieck.ι (projectiveTelescopeDiagram R) n)
        (classifyingSpaceMap (projectiveStageRight R P) x))
      (classifyingSpaceMap (Grothendieck.ι (projectiveTelescopeDiagram R) n)
        (classifyingSpaceMap (projectiveStageRight R P) y)) ↔
    Joined (classifyingSpaceMap (Grothendieck.ι (projectiveTelescopeDiagram R) n) x)
      (classifyingSpaceMap (Grothendieck.ι (projectiveTelescopeDiagram R) n) y) := by
  let H := classifyingSpaceNaturalTransformationHomotopy (projectiveStageRightLeftIso R P).hom
  have hx := (show Joined _ _ from ⟨H.evalAt x⟩).map
    (classifyingSpaceMap (Grothendieck.ι (projectiveTelescopeDiagram R) n)).hom.continuous
  have hy := (show Joined _ _ from ⟨H.evalAt y⟩).map
    (classifyingSpaceMap (Grothendieck.ι (projectiveTelescopeDiagram R) n)).hom.continuous
  constructor
  · intro h
    exact (projectiveStageLeft_infinite_joined_iff R P n x y).mp
      (hx.symm.trans (h.trans hy))
  · intro h
    exact hx.trans (((projectiveStageLeft_infinite_joined_iff R P n x y).mpr h).trans hy.symm)

end ModuleCat.FiniteProjective
