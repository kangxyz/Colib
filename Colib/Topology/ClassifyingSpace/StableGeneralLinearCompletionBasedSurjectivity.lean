/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.StableGeneralLinearCompletionSurjectivity
public import Colib.Topology.ClassifyingSpace.StableGeneralLinearCompletionQuotient
public import Colib.Topology.Homotopy.HomotopyGroup.PathComponentPositive

/-!
# Surjectivity of the original based stable completion map

The original component restriction and the chosen inverse-homotopy basepoint
track transport the finite-matrix representatives to the stable based map.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Topology SSet HomotopyGroup CategoryTheory.Limits MonoidalCategory
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  ModuleCat.FiniteProjective.categoryDirectSumMonoidal
  ModuleCat.FiniteProjective.directSumMonoidal
  ModuleCat.FiniteProjective.directSumSymmetric
  CategoryTheory.Localization.groupoid

namespace ModuleCat.FiniteProjective.StableCompletion
variable (R : Type u) [Ring R]

/-- The original stable-to-telescope map is the forward map of this actual equivalence. -/
def originalStableTelescopeEquiv :
    ContinuousMap.HomotopyEquiv
      (ClassifyingSpace (SingleObj (StableGeneralLinear.Group R)))
      (ClassifyingSpace (StableGeneralLinear.GrothendieckModel.Telescope R)) :=
  (asSmallClassifyingHomeomorph
    (SingleObj (StableGeneralLinear.Group R))).toHomotopyEquiv.trans
      (StableGeneralLinear.GrothendieckModel.classifyingHomotopyEquiv R).symm

/-- The chosen inverse track joins the actual stable basepoint image to rank zero. -/
def sourceBasepointPath :
    Path (originalStableToTelescope R (stableBase R))
      (classifyingSpacePoint (telescopeBase R)) :=
  ((projectionInverseHomotopy R).evalAt (classifyingSpacePoint (telescopeBase R))).cast
    (by
      symm
      change (StableGeneralLinear.GrothendieckModel.classifyingHomotopyEquiv R).invFun
        (classifyingSpaceMap (StableGeneralLinear.GrothendieckModel.projection R)
          (classifyingSpacePoint (telescopeBase R))) = _
      rw [classifyingSpaceMap_point]
      change _ = (StableGeneralLinear.GrothendieckModel.classifyingHomotopyEquiv R).invFun
        (asSmallClassifyingHomeomorph
          (SingleObj (StableGeneralLinear.Group R)) (stableBase R))
      rw [stableBase, asSmallClassifyingHomeomorph_point]
      rfl)
    rfl

/-- The original restriction sends the rank-zero vertex to the actual component basepoint. -/
lemma telescopeZeroMap_point :
    telescopeZeroMap R (classifyingSpacePoint (telescopeBase R)) = zeroBase R := by
  apply Subtype.ext
  exact classifyingSpaceMapUniversal_point (telescopeFunctor R) (telescopeBase R)

/-- The source inverse track maps to precisely the previously chosen based correction path. -/
lemma sourceBasepointPath_map (t : unitInterval) :
    telescopeZeroMap R (sourceBasepointPath R t) = basepointPath R t := rfl

/-- Ambient surjectivity restricts to the actual component through its injective inclusion. -/
lemma telescopeZeroMap_piOne_surjective_of_inclusion
    (hi : Function.Injective (piMap 0
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(ZeroComponent R, ClassifyingSpace (Completion R))) (x := zeroBase R) rfl)) :
    Function.Surjective (piMap 0 (telescopeZeroMap R) (telescopeZeroMap_point R)) := by
  let i : C(ZeroComponent R, ClassifyingSpace (Completion R)) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  intro a
  obtain ⟨b, hb⟩ := telescopeMap_piOne_surjective R (piMap 0 i rfl a)
  refine ⟨b, hi ?_⟩
  change HomotopyGroup.map i rfl
    (HomotopyGroup.map (telescopeZeroMap R) (telescopeZeroMap_point R) b) = _
  rw [← HomotopyGroup.map_comp (telescopeZeroMap R) (telescopeZeroMap_point R) i rfl]
  exact hb

/-- The actual component restriction is surjective on the fundamental group at rank zero. -/
theorem telescopeZeroMap_piOne_surjective :
    Function.Surjective (piMap 0 (telescopeZeroMap R) (telescopeZeroMap_point R)) := by
  apply telescopeZeroMap_piOne_surjective_of_inclusion R
  exact (homotopyGroupMap_pathComponent_bijective (N := Fin 1) (zeroPoint R)).injective

/-- Surjectivity at rank zero transfers through the original inverse and its chosen track. -/
lemma stablePiOneMap_surjective_of_telescope
    (h : Function.Surjective (piMap 0 (telescopeZeroMap R) (telescopeZeroMap_point R))) :
    Function.Surjective (stablePiOneMap R) := by
  have hz : Function.Surjective (HomotopyGroup.map (N := Fin 1)
      (telescopeZeroMap R) (x := classifyingSpacePoint (telescopeBase R)) rfl) := by
    have haux (y : ZeroComponent R)
        (hy : telescopeZeroMap R (classifyingSpacePoint (telescopeBase R)) = y)
        (hs : Function.Surjective (piMap 0 (telescopeZeroMap R) hy)) :
        Function.Surjective (piMap 0 (telescopeZeroMap R)
          (x := classifyingSpacePoint (telescopeBase R)) rfl) := by
      subst y
      exact hs
    exact haux _ (telescopeZeroMap_point R) h
  have ht := (homotopyGroupMap_surjective_iff_of_path (telescopeZeroMap R)
    (sourceBasepointPath R) 1).mpr hz
  have he := (homotopyGroupMap_bijective_of_homotopyEquiv
    (originalStableTelescopeEquiv R) (x := stableBase R) rfl 1).surjective
  have hc : Function.Surjective (piMap 0 (stableZeroMap R) (x := stableBase R) rfl) := by
    intro a
    obtain ⟨b, hb⟩ := ht a
    obtain ⟨c, hc⟩ := he b
    refine ⟨c, ?_⟩
    change HomotopyGroup.map ((telescopeZeroMap R).comp (originalStableToTelescope R)) rfl c = a
    rw [HomotopyGroup.map_comp (originalStableToTelescope R) rfl (telescopeZeroMap R) rfl]
    exact (congrArg (HomotopyGroup.map (telescopeZeroMap R) rfl) hc).trans hb
  exact (pathTransportMulEquiv (basepointPath R) 0).surjective.comp hc

/-- The original based stable completion map is surjective on the genuine fundamental group. -/
theorem stablePiOneMap_surjective : Function.Surjective (stablePiOneMap R) :=
  stablePiOneMap_surjective_of_telescope R (telescopeZeroMap_piOne_surjective R)

/-- Every zero-component fundamental-group element is represented by an original stable matrix. -/
theorem stableGroupPiOneMap_surjective : Function.Surjective (stableGroupPiOneMap R) :=
  (stablePiOneMap_surjective R).comp
    (GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group R)).surjective

/-- The previously constructed actual elementary-quotient factor is surjective. -/
theorem elementaryPiOneFactor_surjective : Function.Surjective (elementaryPiOneFactor R) := by
  intro a
  obtain ⟨g, hg⟩ := stableGroupPiOneMap_surjective R a
  exact ⟨StableGeneralLinear.quotientMap R g, hg⟩

end ModuleCat.FiniteProjective.StableCompletion
