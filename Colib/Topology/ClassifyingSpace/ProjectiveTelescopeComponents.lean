/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.ProjectiveTelescope
public import Colib.Topology.ClassifyingSpace.TranslationTelescopeComponents

/-!
Adapted from `Quillen/KTheory/Plus/ProjectiveTelescopeComponents.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original projective
complements, stage maps and coefficient transports are retained.

# Component bijectivity of actual projective telescope translations

Free powers act bijectively on components because the rank-one left action
agrees componentwise with the genuine right-stabilization equivalence. A
projective complement then proves the claim for every projective right module,
without rank cancellation, invariant basis number, or a stable-freeness assumption.
-/

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

/-- The actual left translation by any labelled free power reflects components. -/
theorem projectiveTelescope_power_reflects_joined (n : ℕ)
    (x y : ClassifyingSpace (ProjectiveTelescope R))
    (h : Joined (classifyingSpaceMap
      (projectiveTelescopeTranslation R (rankOnePower Rᵐᵒᵖ n)) x)
      (classifyingSpaceMap (projectiveTelescopeTranslation R (rankOnePower Rᵐᵒᵖ n)) y)) :
    Joined x y := by
  induction n generalizing x y with
  | zero =>
    exact (TranslationTelescope.leftTranslation_unit_joined (freeIso Rᵐᵒᵖ 1) x).symm.trans
      (h.trans (TranslationTelescope.leftTranslation_unit_joined (freeIso Rᵐᵒᵖ 1) y))
  | succ n ih =>
    exact TranslationTelescope.leftTranslation_tensor_reflects_joined
      (freeIso Rᵐᵒᵖ 1) (freeIso Rᵐᵒᵖ 1) (rankOnePower Rᵐᵒᵖ n)
      (fun a b hab ↦ (TranslationTelescope.generator_joined_iff _ a b).mp hab) ih x y h

/-- Every component is reached by every original free-power translation. -/
theorem projectiveTelescope_power_surjective_components (n : ℕ)
    (y : ClassifyingSpace (ProjectiveTelescope R)) :
    ∃ x, Joined (classifyingSpaceMap
      (projectiveTelescopeTranslation R (rankOnePower Rᵐᵒᵖ n)) x) y := by
  induction n generalizing y with
  | zero => exact ⟨y, TranslationTelescope.leftTranslation_unit_joined _ y⟩
  | succ n ih =>
    exact TranslationTelescope.leftTranslation_tensor_surjective_components
      (freeIso Rᵐᵒᵖ 1) (freeIso Rᵐᵒᵖ 1) (rankOnePower Rᵐᵒᵖ n)
      (TranslationTelescope.exists_joined_generator _) ih y

/-- Adding any projective right module preserves and reflects the component relation. -/
theorem projectiveTelescopeTranslation_joined_iff (P : IsoCategory Rᵐᵒᵖ)
    (x y : ClassifyingSpace (ProjectiveTelescope R)) :
    Joined (classifyingSpaceMap (projectiveTelescopeTranslation R P) x)
      (classifyingSpaceMap (projectiveTelescopeTranslation R P) y) ↔ Joined x y := by
  obtain ⟨n, Q, ⟨f⟩⟩ := rankOne_cofinal Rᵐᵒᵖ P
  constructor
  · exact TranslationTelescope.leftTranslation_reflects_joined_of_complement
      (freeIso Rᵐᵒᵖ 1) P Q (rankOnePower Rᵐᵒᵖ n) f
      (projectiveTelescope_power_reflects_joined R n) x y
  · exact fun h ↦ h.map (classifyingSpaceMap (projectiveTelescopeTranslation R P)).hom.continuous

/-- Every projective right-module translation reaches every component. -/
theorem projectiveTelescopeTranslation_surjective_components (P : IsoCategory Rᵐᵒᵖ)
    (y : ClassifyingSpace (ProjectiveTelescope R)) :
    ∃ x, Joined (classifyingSpaceMap (projectiveTelescopeTranslation R P) x) y := by
  obtain ⟨n, Q, ⟨f⟩⟩ := rankOne_cofinal Rᵐᵒᵖ P
  exact TranslationTelescope.leftTranslation_surjective_components_of_complement
    (freeIso Rᵐᵒᵖ 1) P Q (rankOnePower Rᵐᵒᵖ n) f
    (projectiveTelescope_power_surjective_components R n) y

end ModuleCat.FiniteProjective
