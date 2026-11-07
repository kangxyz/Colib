/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Colib.Topology.ClassifyingSpace.ProjectiveTelescopeAbelianHomology
import Colib.Topology.ClassifyingSpace.ProjectiveTelescopeComma
import Colib.Topology.LocalCoefficients.GroupCompletionAbelian

open CategoryTheory FundamentalGroupoid.LocalCoefficients
open ModuleCat.FiniteProjective

universe u

variable (R : Type u) [Ring R]

-- The original projective translation, with no invariance premise.
example (P : IsoCategory Rᵐᵒᵖ)
    (A : System.{u + 1, u + 1} (ClassifyingSpace (ProjectiveTelescope R)))
    (hA : AbelianMonodromy A) (n : ℕ) :
    IsIso (pushforwardHomologyMap
      (classifyingSpaceMap (projectiveTelescopeTranslation R P)).hom A n) :=
  projectiveTelescopeTranslation_abelianHomology_isIso R P A hA n

-- Surjectivity requires no abelian restriction on the target system.
example (P : IsoCategory Rᵐᵒᵖ)
    (A : System.{u + 1, u + 1} (ClassifyingSpace (ProjectiveTelescope R))) (n : ℕ) :
    Function.Surjective (pushforwardHomologyMap
      (classifyingSpaceMap (projectiveTelescopeTranslation R P)).hom A n) :=
  projectiveTelescopeTranslation_homology_surjective R P A n

#print axioms ModuleCat.FiniteProjective.projectiveTelescopeTranslation_abelianHomology_isIso
#print axioms ModuleCat.FiniteProjective.projectiveTelescopeTranslation_homology_surjective
#print axioms CategoryTheory.MonoidalCategory.TranslationTelescope.monoidalLeftAction

#print axioms ModuleCat.FiniteProjective.projectiveTelescopeProjection_comma_abelianHomology_isIso
#print axioms ModuleCat.FiniteProjective.projectiveTelescopeReplacementEntry_source
#print axioms CategoryTheory.GroupCompletion.Localization.classifyingSpace_abelianMonodromy
