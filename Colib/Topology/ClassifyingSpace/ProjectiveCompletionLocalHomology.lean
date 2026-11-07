/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Topology.ClassifyingSpace.ProjectiveTelescopeUnitHomology
public import Colib.Topology.ClassifyingSpace.ProjectiveCompletionUnitHomotopy
public import Colib.Topology.LocalCoefficients.GroupCompletionAbelian
public import Colib.Topology.LocalCoefficients.HomotopySquare

/-!
Adapted from `Quillen/KTheory/Plus/ProjectiveCompletionLocalHomology.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The literal native stable map is retained.

# All target local systems for the original completion map

The original abelian-coefficient unit comparison is transported through the
actual completed interchange and retraction. Commutativity of loops on every
component of the completion supplies the abelian monodromy of each pulled-back
system. All coefficient conversions are the actual homotopy-square conversions.
-/
@[expose] public section

open CategoryTheory.GroupCompletion
open FundamentalGroupoid.LocalCoefficients

noncomputable section
open CategoryTheory MonoidalCategory FundamentalGroupoid
universe u
namespace ModuleCat.FiniteProjective.StableFreeRight
open GroupCompletion LocalCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal directSumSymmetric
  projectiveTelescopeAction
variable (R : Type u) [Ring R]

/-- The original completion functor preserves every target-system homology group. -/
theorem completionFunctor_localHomology_isIso
    (A : System.{u + 1, u + 1} (ClassifyingSpace (StableCompletion.Completion R)))
    (n : ℕ) : IsIso (pushforwardHomologyMap
      (classifyingSpaceMapUniversal (completionFunctor R)) A n) := by
  let E := projectiveTelescopeInterchangeHomotopyEquiv R
  let K := completedRetractionHomotopyEquiv R
  let v := classifyingSpaceMapUniversal
    (TranslationTelescope.telescopeUnit (freeIso Rᵐᵒᵖ 1))
  let f := classifyingSpaceMapUniversal
    (Localization.unitEntry (C := IsoCategory Rᵐᵒᵖ) (D := ProjectiveTelescope R))
  let g := classifyingSpaceMapUniversal (completionFunctor R)
  have hf : f = E.toFun.comp v := by
    dsimp only [f, E, v]
    rw [projectiveTelescopeInterchangeHomotopyEquiv_toFun,
      ← classifyingSpaceMapUniversal_comp, telescopeUnit_interchange_unit]
  have hK : (K.toFun.comp v).Homotopy g := telescopeUnitCompletionHomotopy R
  have hE : ((E.symm.trans K).toFun.comp f).Homotopy (K.toFun.comp v) := by
    rw [hf]
    exact (ContinuousMap.Homotopy.refl K.toFun).comp
      (E.left_inv.some.compContinuousMap v)
  have H : (g.comp (ContinuousMap.HomotopyEquiv.refl _).toFun).Homotopy
      ((E.symm.trans K).toFun.comp f) := hK.symm.trans hE.symm
  apply isIso_pushforwardHomologyMap_of_homotopySquare
    (ContinuousMap.HomotopyEquiv.refl _) (E.symm.trans K) f g H A n
  apply projectiveTelescopeUnit_abelian_homology_isIso
  exact pullback_abelianMonodromy _ (Localization.classifyingSpace_abelianMonodromy A)

/-- The actual original completion map is a quasi-isomorphism for every target system. -/
theorem completionFunctor_localCoefficients_quasiIso
    (A : System.{u + 1, u + 1} (ClassifyingSpace (StableCompletion.Completion R))) :
    QuasiIso (pushforwardChainMap
      (classifyingSpaceMapUniversal (completionFunctor R)) A) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact completionFunctor_localHomology_isIso R A n

end ModuleCat.FiniteProjective.StableFreeRight
