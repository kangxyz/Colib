/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.ProjectiveTelescopeSurjectivity
public import Colib.Topology.ClassifyingSpace.ProjectiveStageComponents
public import Colib.Topology.LocalCoefficients.TelescopeTranslationKernel
public import Colib.Topology.LocalCoefficients.AbelianHomotopySplitting

/-!
Adapted from `Quillen/KTheory/Plus/ProjectiveTelescopeAbelianHomology.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original projective
complements, stage maps and coefficient transports are retained.
 # Abelian local homology of original projective telescope translations -/

@[expose] public section

open FundamentalGroupoid.LocalCoefficients

noncomputable section
open CategoryTheory MonoidalCategory Grothendieck
universe u
namespace ModuleCat.FiniteProjective
open FundamentalGroupoid.LocalCoefficients
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal directSumSymmetric
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable (R : Type u) [Ring R]

/-- The original finite-stage associator commutes left and right addition. -/
def projectiveStageLeftRightIso (P Q : IsoCategory Rᵐᵒᵖ) :
    projectiveStageLeft R P ⋙ projectiveStageRight R Q ≅
      projectiveStageRight R Q ⋙ projectiveStageLeft R P :=
  Functor.isoWhiskerLeft AsSmall.down
    (Functor.isoWhiskerRight (TranslationTelescope.leftRightCommutationIso P Q) AsSmall.up)

/-- The actual associator track ends at the original infinite left translation. -/
def projectiveStageCommutationIso (P Q : IsoCategory Rᵐᵒᵖ) (m : ℕ) :
    projectiveStageLeft R P ⋙ projectiveStageRight R Q ⋙
      Grothendieck.ι (projectiveTelescopeDiagram R) m ≅
    projectiveStageRight R Q ⋙ Grothendieck.ι (projectiveTelescopeDiagram R) m ⋙
      projectiveTelescopeTranslation R P :=
  Functor.isoWhiskerRight (projectiveStageLeftRightIso R P Q)
    (Grothendieck.ι (projectiveTelescopeDiagram R) m) ≪≫
    eqToIso (by rw [projectiveTelescopeTranslation_stage]; rfl)

/-- Realization retains the original associator commuting homotopy. -/
def projectiveStageCommutationHomotopy (P Q : IsoCategory Rᵐᵒᵖ) (m : ℕ) :
    (((classifyingSpaceMap (Grothendieck.ι (projectiveTelescopeDiagram R) m)).hom.comp
      (classifyingSpaceMap (projectiveStageRight R Q)).hom).comp
        (classifyingSpaceMap (projectiveStageLeft R P)).hom).Homotopy
    ((classifyingSpaceMap (projectiveTelescopeTranslation R P)).hom.comp
      ((classifyingSpaceMap (Grothendieck.ι (projectiveTelescopeDiagram R) m)).hom.comp
        (classifyingSpaceMap (projectiveStageRight R Q)).hom)) := by
  simpa only [classifyingSpaceMap_comp, TopCat.hom_comp, ContinuousMap.comp_assoc] using
    classifyingSpaceNaturalTransformationHomotopy (projectiveStageCommutationIso R P Q m).hom

/-- A class killed by the original translation is zero for abelian monodromy. -/
theorem projectiveTelescopeTranslation_homology_kernel_zero (P : IsoCategory Rᵐᵒᵖ)
    (A : System.{u + 1, u + 1} (ClassifyingSpace (ProjectiveTelescope R)))
    (hA : AbelianMonodromy A) (d : ℕ)
    (x : homology (pullback (classifyingSpaceMap (projectiveTelescopeTranslation R P)).hom A) d)
    (hx : pushforwardHomologyMap
      (classifyingSpaceMap (projectiveTelescopeTranslation R P)).hom A d x = 0) : x = 0 := by
  obtain ⟨n, y, s, hy, hz, hc, hs⟩ :=
    TranslationTelescope.translation_kernel_exists_stable_support (freeIso Rᵐᵒᵖ 1) P A d x hx
  obtain ⟨k, Q, ⟨c⟩⟩ := exists_complement_iso_freeIso Rᵐᵒᵖ P
  have he := abelian_homotopy_splitting_kernel_zero
    (classifyingSpaceMap (Grothendieck.ι (projectiveTelescopeDiagram R) n)).hom
    (classifyingSpaceMap (projectiveTelescopeTranslation R P)).hom
    (classifyingSpaceMap (projectiveStageLeft R P)).hom
    ((classifyingSpaceMap (Grothendieck.ι (projectiveTelescopeDiagram R) (n + k))).hom.comp
      (classifyingSpaceMap (projectiveStageRight R Q)).hom)
    (TranslationTelescope.stageTranslation_square (freeIso Rᵐᵒᵖ 1) P n)
    (projectiveStageFactorizationHomotopy R P Q k n c)
    (projectiveStageCommutationHomotopy R P Q (n + k))
    (fun a b hab ↦ (projectiveTelescopeTranslation_joined_iff R P a b).mp hab)
    A hA d y s hc hs hz
  exact hy.symm.trans he

/-- The original translation is injective on homology with abelian monodromy. -/
theorem projectiveTelescopeTranslation_homology_injective (P : IsoCategory Rᵐᵒᵖ)
    (A : System.{u + 1, u + 1} (ClassifyingSpace (ProjectiveTelescope R)))
    (hA : AbelianMonodromy A) (d : ℕ) :
    Function.Injective (pushforwardHomologyMap
      (classifyingSpaceMap (projectiveTelescopeTranslation R P)).hom A d) := by
  intro x y h
  apply sub_eq_zero.mp
  apply projectiveTelescopeTranslation_homology_kernel_zero R P A hA d
  rw [map_sub, h, sub_self]

/-- Every actual precompletion left translation is an abelian local homology
isomorphism; no homology-fibration or group-completion theorem is assumed. -/
theorem projectiveTelescopeTranslation_abelianHomology_isIso (P : IsoCategory Rᵐᵒᵖ)
    (A : System.{u + 1, u + 1} (ClassifyingSpace (ProjectiveTelescope R)))
    (hA : AbelianMonodromy A) (d : ℕ) :
    IsIso (pushforwardHomologyMap
      (classifyingSpaceMap (projectiveTelescopeTranslation R P)).hom A d) := by
  have : Mono (pushforwardHomologyMap
      (classifyingSpaceMap (projectiveTelescopeTranslation R P)).hom A d) :=
    (ModuleCat.mono_iff_injective _).mpr
      (projectiveTelescopeTranslation_homology_injective R P A hA d)
  have := projectiveTelescopeTranslation_homology_epi R P A d
  exact isIso_of_mono_of_epi _

end ModuleCat.FiniteProjective
