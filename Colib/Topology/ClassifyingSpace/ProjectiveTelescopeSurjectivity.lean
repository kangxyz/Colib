/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.ProjectiveTelescopeFactorization
public import Colib.Topology.LocalCoefficients.TelescopeHomologyElements
public import Colib.Topology.LocalCoefficients.HomologyFactorization

/-!
Adapted from `Quillen/KTheory/Plus/ProjectiveTelescopeSurjectivity.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original projective
complements, stage maps and coefficient transports are retained.

# Surjectivity of actual projective telescope translations

The original finite-stage complement factorization supplies the homotopy. Every
class has an original-stage representative, so the actual translation homology
map is surjective with every target local coefficient system.
-/

@[expose] public section

open FundamentalGroupoid.LocalCoefficients

noncomputable section
open CategoryTheory MonoidalCategory Grothendieck
universe u

namespace ModuleCat.FiniteProjective
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open FundamentalGroupoid.LocalCoefficients
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal directSumSymmetric
variable (R : Type u) [Ring R]

/-- The original finite-stage factorization realizes to a specified homotopy
through the actual precompletion translation. -/
def projectiveStageFactorizationHomotopy (P Q : IsoCategory Rᵐᵒᵖ) (k n : ℕ)
    (f : P ⊗ Q ≅ freeIso Rᵐᵒᵖ k) :
    (classifyingSpaceMap (Grothendieck.ι (projectiveTelescopeDiagram R) n)).hom.Homotopy
      ((classifyingSpaceMap (projectiveTelescopeTranslation R P)).hom.comp
        ((classifyingSpaceMap (Grothendieck.ι (projectiveTelescopeDiagram R) (n + k))).hom.comp
          (classifyingSpaceMap (AsSmall.down ⋙ MonoidalCategory.tensorRight Q ⋙
            AsSmall.up)).hom)) := by
  simpa only [classifyingSpaceMap_comp, TopCat.hom_comp, ContinuousMap.comp_assoc] using
    classifyingSpaceNaturalTransformationHomotopy
      (projectiveStageFactorizationNatTrans R P Q k n f)

/-- The actual left translation is surjective on homology for all target systems. -/
theorem projectiveTelescopeTranslation_homology_surjective (P : IsoCategory Rᵐᵒᵖ)
    (A : System.{u + 1, u + 1} (ClassifyingSpace (ProjectiveTelescope R))) (k : ℕ) :
    Function.Surjective (pushforwardHomologyMap
      (classifyingSpaceMap (projectiveTelescopeTranslation R P)).hom A k) := by
  intro x
  obtain ⟨n, y, hy⟩ := Grothendieck.Telescope.localHomology_exists_stage
    (projectiveTelescopeDiagram R) A k x
  obtain ⟨m, Q, ⟨f⟩⟩ := exists_complement_iso_freeIso Rᵐᵒᵖ P
  obtain ⟨z, hz⟩ := exists_preimage_of_homotopy_factorization _ _ _
    (projectiveStageFactorizationHomotopy R P Q m n f) A k y
  exact ⟨z, hz.trans hy⟩

/-- Categorical epimorphism form of the actual all-target surjectivity theorem. -/
theorem projectiveTelescopeTranslation_homology_epi (P : IsoCategory Rᵐᵒᵖ)
    (A : System.{u + 1, u + 1} (ClassifyingSpace (ProjectiveTelescope R))) (k : ℕ) :
    Epi (pushforwardHomologyMap
      (classifyingSpaceMap (projectiveTelescopeTranslation R P)).hom A k) :=
  (ModuleCat.epi_iff_surjective _).mpr
    (projectiveTelescopeTranslation_homology_surjective R P A k)

end ModuleCat.FiniteProjective
