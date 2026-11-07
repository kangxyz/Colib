/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Topology.ClassifyingSpace.StableProjectiveCompletion
public import Colib.Topology.ClassifyingSpace.ProjectiveTelescopeComponents
public import Colib.CategoryTheory.GroupCompletion.UnitRoofs
public import Colib.Topology.ClassifyingSpace.CompletionSurjectivity

/-!
Adapted from `Quillen/KTheory/Plus/ProjectiveCompletionComponents.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual objects,
functors, coefficient universes and comparison maps.

# The exact zero-component preimage of the original completion map

Actual completed roofs yield a common projective stabilization. Reflection of
components by that original telescope translation then detects the original
zero component, without an assumed grading or rank cancellation.
-/
@[expose] public section

open CategoryTheory.GroupCompletion

noncomputable section
open CategoryTheory MonoidalCategory Grothendieck
open scoped MonoidalLeftAction
universe u
namespace ModuleCat.FiniteProjective.StableFreeRight
open GroupCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal directSumSymmetric
  CategoryTheory.Localization.groupoid
variable (R : Type u) [Ring R]

/-- An actual path to completed zero supplies an actual common projective stabilization. -/
theorem exists_stabilizedHom_of_completed_joined (n : ℕ) (P : IsoCategory Rᵐᵒᵖ)
    (h : Joined (classifyingSpacePoint (⟨rankOnePower Rᵐᵒᵖ n, P⟩ : StableCompletion.Completion R))
      (StableCompletion.zeroPoint R)) :
    ∃ s : IsoCategory Rᵐᵒᵖ, Nonempty (s ⊗ P ⟶ s ⊗ rankOnePower Rᵐᵒᵖ n) := by
  obtain ⟨a, -⟩ := classifyingGroupoidCompletionFunctor_map_surjective
    (StableCompletion.Completion R) ⟨rankOnePower Rᵐᵒᵖ n, P⟩ (StableCompletion.stageObject R 0)
    (FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk h.somePath))
  obtain ⟨⟨A, B⟩, p, q, -⟩ := CategoryTheory.Localization.exists_right_roof
    ActionLocalization.exists_common_right_multiple a
  obtain ⟨f, -⟩ := Localization.unitArrow_surjective A B q
  obtain ⟨r, -⟩ := ActionLocalization.mkHom_surjective
    (rankOnePower Rᵐᵒᵖ n, P) (A, B) p
  exact ⟨r.denom, ⟨r.map.2 ≫ inv f ≫ inv r.map.1⟩⟩

/-- At every original stage, completed-zero membership reflects the actual telescope component. -/
theorem completionFunctor_vertex_reflects_zero (n : ℕ) (P : IsoCategory Rᵐᵒᵖ)
    (h : Joined (classifyingSpacePoint ((completionFunctor R).obj ⟨n, AsSmall.up.obj P⟩))
      (StableCompletion.zeroPoint R)) :
    Joined (classifyingSpacePoint (⟨n, AsSmall.up.obj P⟩ : ProjectiveTelescope R))
      (classifyingSpacePoint (projectiveTelescopeBase R)) := by
  obtain ⟨s, ⟨f⟩⟩ := exists_stabilizedHom_of_completed_joined R n P h
  have hs : Joined
      (classifyingSpaceMap (projectiveTelescopeTranslation R s)
        (classifyingSpacePoint (⟨n, AsSmall.up.obj P⟩ : ProjectiveTelescope R)))
      (classifyingSpaceMap (projectiveTelescopeTranslation R s)
        (classifyingSpacePoint (stageObject R n))) := by
    rw [classifyingSpaceMap_point, classifyingSpaceMap_point]
    exact ⟨classifyingSpacePath
      ((Grothendieck.ι (projectiveTelescopeDiagram R) n).map (AsSmall.up.map f))⟩
  have hp := (projectiveTelescopeTranslation_joined_iff R s _ _).mp hs
  have hn : Joined (classifyingSpacePoint (projectiveTelescopeBase R))
      (classifyingSpacePoint (stageObject R n)) :=
    ⟨classifyingSpacePath ((stageSequence R).map (homOfLE (Nat.zero_le n)))⟩
  exact hp.trans hn.symm

/-- The actual completion map reflects its original zero path component at every point. -/
theorem completionMap_reflects_zero (x : ClassifyingSpace (ProjectiveTelescope R))
    (h : Joined ((classifyingSpaceMapUniversal (completionFunctor R)) x)
      (StableCompletion.zeroPoint R)) :
    Joined x (classifyingSpacePoint (projectiveTelescopeBase R)) := by
  obtain ⟨⟨n, ⟨P⟩⟩, hx⟩ := classifyingSpace_joined_vertex x
  have hv := (hx.map (classifyingSpaceMapUniversal (completionFunctor R)).continuous).trans h
  rw [classifyingSpaceMapUniversal_point] at hv
  exact hx.symm.trans (completionFunctor_vertex_reflects_zero R n P hv)

/-- The preimage of the genuine completed zero component is exactly the chosen
original projective telescope component. -/
theorem completionMap_preimage_zeroComponent :
    (classifyingSpaceMapUniversal (completionFunctor R)) ⁻¹'
      pathComponent (StableCompletion.zeroPoint R) =
    pathComponent (classifyingSpacePoint (projectiveTelescopeBase R)) := by
  ext x
  constructor
  · intro h
    exact (completionMap_reflects_zero R x h.symm).symm
  · intro h
    have hh := h.map (classifyingSpaceMapUniversal (completionFunctor R)).continuous
    simp only [classifyingSpaceMapUniversal_point, completionFunctor_base] at hh
    exact hh

end ModuleCat.FiniteProjective.StableFreeRight
