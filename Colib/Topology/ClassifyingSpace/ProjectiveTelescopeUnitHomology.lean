/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Topology.ClassifyingSpace.ProjectiveTelescopeComma
public import Colib.CategoryTheory.TheoremA.InitialHomology

/-!
Adapted from `Quillen/KTheory/Plus/ProjectiveTelescopeUnitHomology.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original unit and comma maps are retained.

# Abelian local homology of the original projective telescope unit

The genuine initial-comma comparison applies to the original strict comma
diagram. The actual comma-entry adjunction and exact unit square identify its
map with the original unit; no homology-fibration premise is introduced.
-/
@[expose] public section

open CategoryTheory.GroupCompletion
open FundamentalGroupoid.LocalCoefficients

noncomputable section
open CategoryTheory MonoidalCategory FundamentalGroupoid
universe u
namespace ModuleCat.FiniteProjective
open GroupCompletion LocalCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal directSumSymmetric
  projectiveTelescopeAction
variable (R : Type u) [Ring R]

/-- The original projective-telescope unit preserves actual abelian local-coefficient chains. -/
theorem projectiveTelescopeUnit_abelian_quasiIso
    (A : System.{u + 1, u + 1} (ClassifyingSpace (ProjectiveTelescopeLocalization R)))
    (hA : AbelianMonodromy A) :
    QuasiIso (pushforwardChainMap (classifyingSpaceMapUniversal
      (Localization.unitEntry (C := IsoCategory Rᵐᵒᵖ) (D := ProjectiveTelescope R))) A) := by
  let : ∀ P : IsoCategory Rᵐᵒᵖ, (tensorRight P).Faithful := directSumRight_faithful Rᵐᵒᵖ
  let i : ActionLocalization (IsoCategory Rᵐᵒᵖ) (IsoCategory Rᵐᵒᵖ) := ⟨𝟙_ _⟩
  let hi : CategoryTheory.Limits.IsInitial i := ActionLocalization.selfUnitIsInitial
  let q := classifyingSpaceMapUniversal
    (CostructuredArrow.proj (projectiveTelescopeProjection R) i)
  let j := classifyingSpaceMapUniversal
    (Localization.commaEntry (D := ProjectiveTelescope R) (𝟙_ (IsoCategory Rᵐᵒᵖ)))
  have hq : QuasiIso (pushforwardChainMap q A) := by
    have h := TheoremA.commaInitialProjection_abelian_quasiIso
      (projectiveTelescopeProjection R) i hi (fun d B hB ↦ ?_) A hA
    · exact (congrArg (fun f => QuasiIso (pushforwardChainMap f A))
        (classifyingSpaceMapUniversal_eq
          (CostructuredArrow.proj (projectiveTelescopeProjection R) i))).mpr h
    · rw [quasiIso_iff]
      intro n
      rw [quasiIsoAt_iff_isIso_homologyMap]
      exact projectiveTelescopeCommaDiagram_map_abelianHomology_isIso R (hi.to d) B hB n
  have hj : QuasiIso (pushforwardChainMap j (pullback q A)) := by
    exact pushforwardChainMap_quasiIso_of_homotopyEquiv
      (Localization.commaEntryClassifyingHomotopyEquiv (D := ProjectiveTelescope R)
        (𝟙_ (IsoCategory Rᵐᵒᵖ))) (pullback q A)
  have hc := pushforwardChainMap_quasiIso_comp j q A hj hq
  have hw : q.comp j = classifyingSpaceMapUniversal
      (Localization.unitEntry (C := IsoCategory Rᵐᵒᵖ) (D := ProjectiveTelescope R)) := by
    dsimp only [q, j]
    erw [← classifyingSpaceMapUniversal_comp, ← Localization.unitEntry_eq_comma]
  rw [hw] at hc
  exact hc

/-- The same theorem retains every degree of the original induced local homology map. -/
theorem projectiveTelescopeUnit_abelian_homology_isIso
    (A : System.{u + 1, u + 1} (ClassifyingSpace (ProjectiveTelescopeLocalization R)))
    (hA : AbelianMonodromy A) (n : ℕ) :
    IsIso (pushforwardHomologyMap (classifyingSpaceMapUniversal
      (Localization.unitEntry (C := IsoCategory Rᵐᵒᵖ) (D := ProjectiveTelescope R))) A n) := by
  exact (quasiIsoAt_iff_isIso_homologyMap _ n).mp
    ((quasiIso_iff _).mp (projectiveTelescopeUnit_abelian_quasiIso R A hA) n)

end ModuleCat.FiniteProjective
