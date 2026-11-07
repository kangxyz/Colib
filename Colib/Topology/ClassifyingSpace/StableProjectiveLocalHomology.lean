/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.ProjectiveCompletionLocalHomology
public import Colib.Topology.ClassifyingSpace.ProjectiveCompletionComponents
public import Colib.Topology.ClassifyingSpace.StableProjectiveSource
public import Colib.Topology.LocalCoefficients.ComponentComparison
public import Colib.Topology.LocalCoefficients.MapQuasiIso
public import Colib.Topology.LocalCoefficients.HomotopyQuasiIso
public import Colib.Topology.LocalCoefficients.UniverseLift

/-!
Adapted from `Quillen/KTheory/Plus/StableProjectiveLocalHomology.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The literal native stable map is retained.

# All target local coefficients for the original stable completion map

The actual completion map is restricted using its proved zero-component
preimage. Arbitrary systems on that component are handled by genuine extension
by zero. The original stable-source homotopy equivalence then gives the original
stable map, with an explicit source universe lift. The final chain map uses the
existing arbitrary-universe interface, retaining the original continuous map.
-/

@[expose] public section

noncomputable section
open CategoryTheory FundamentalGroupoid
universe u

namespace ModuleCat.FiniteProjective.StableFreeRight

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] categoryDirectSumMonoidal directSumMonoidal directSumSymmetric

variable (R : Type u) [Ring R]

/-- The original completion map has precisely the specified zero-component preimage. -/
lemma completionMap_mem_zero_iff (z : ClassifyingSpace (ProjectiveTelescope R)) :
    classifyingSpaceMapUniversal (completionFunctor R) z ∈
        pathComponent (StableCompletion.zeroPoint R) ↔
      z ∈ pathComponent (classifyingSpacePoint (projectiveTelescopeBase R)) := by
  change z ∈ (classifyingSpaceMapUniversal (completionFunctor R)) ⁻¹'
      pathComponent (StableCompletion.zeroPoint R) ↔ _
  rw [completionMap_preimage_zeroComponent]

/-- The literal restriction of the original projective completion map. -/
def completionZeroMap :
    C(pathComponent (classifyingSpacePoint (projectiveTelescopeBase R)),
      StableCompletion.ZeroComponent R) :=
  LocalCoefficients.componentMap (classifyingSpaceMapUniversal (completionFunctor R))
    (classifyingSpacePoint (projectiveTelescopeBase R)) (StableCompletion.zeroPoint R)
    (completionMap_mem_zero_iff R)

/-- Every system on the actual zero component is preserved by the original restricted map. -/
theorem completionZeroMap_localCoefficients_quasiIso
    (A : LocalCoefficients.System.{u + 1, u + 1} (StableCompletion.ZeroComponent R)) :
    QuasiIso (LocalCoefficients.pushforwardChainMap (completionZeroMap R) A) :=
  LocalCoefficients.componentMap_quasiIso _ _ _ (completionMap_mem_zero_iff R)
    (completionFunctor_localCoefficients_quasiIso R) A

/-- The original stable-source equivalence, with only its domain lifted to the common universe. -/
def stableProjectiveZeroLiftHomotopyEquiv :
    ContinuousMap.HomotopyEquiv
      (ULift.{u + 1} (ClassifyingSpace (SingleObj (StableGeneralLinear.Group R))))
      (pathComponent (classifyingSpacePoint (projectiveTelescopeBase R))) :=
  Homeomorph.ulift.{u + 1, u}.toHomotopyEquiv.trans (stableProjectiveZeroHomotopyEquiv R)

/-- The original stable map after the actual source-lift projection. -/
def stableZeroLiftMap :
    C(ULift.{u + 1} (ClassifyingSpace (SingleObj (StableGeneralLinear.Group R))),
      StableCompletion.ZeroComponent R) :=
  (StableCompletion.stableZeroMap R).comp
    (LocalCoefficients.UniverseLift.down
      (ClassifyingSpace (SingleObj (StableGeneralLinear.Group R))))

/-- The source model and restricted completion retain exactly the original stable map. -/
lemma completionZeroMap_stableProjectiveZeroLift :
    (completionZeroMap R).comp (stableProjectiveZeroLiftHomotopyEquiv R).toFun =
      stableZeroLiftMap R := by
  ext z : 1
  apply Subtype.ext
  change classifyingSpaceMapUniversal (completionFunctor R)
      (stableProjectiveZeroHomotopyEquiv R z.down).val =
    (StableCompletion.stableZeroMap R z.down).val
  rw [stableProjectiveZeroHomotopyEquiv_val]
  exact stableZeroMap_completionMap_val R z.down

/-- The original source-lifted stable map preserves every target system in the common universe. -/
theorem stableZeroLiftMap_localCoefficients_quasiIso
    (A : LocalCoefficients.System.{u + 1, u + 1} (StableCompletion.ZeroComponent R)) :
    QuasiIso (LocalCoefficients.pushforwardChainMap (stableZeroLiftMap R) A) := by
  rw [← completionZeroMap_stableProjectiveZeroLift]
  apply LocalCoefficients.pushforwardChainMap_quasiIso_comp
  · exact LocalCoefficients.pushforwardChainMap_quasiIso_of_homotopyEquiv
      (stableProjectiveZeroLiftHomotopyEquiv R) _
  · exact completionZeroMap_localCoefficients_quasiIso R A

/-- The genuine arbitrary-universe chain map of the original stable completion map
is a quasi-isomorphism for every target system in the stated coefficient universe. -/
theorem stableZeroMap_localCoefficients_quasiIso
    (A : LocalCoefficients.System.{u + 1, u + 1} (StableCompletion.ZeroComponent R)) :
    QuasiIso (LocalCoefficients.UniverseLift.chainMap.{u, u + 1, u + 1}
      (StableCompletion.stableZeroMap R) A) := by
  let B := LocalCoefficients.UniverseLift.system.{u + 1, u + 1, u} A
  have hup : QuasiIso (LocalCoefficients.pushforwardChainMap
      (LocalCoefficients.UniverseLift.up.{u + 1, u + 1} (StableCompletion.ZeroComponent R)) B) :=
    LocalCoefficients.pushforwardChainMap_quasiIso_of_homotopyEquiv
      (Homeomorph.ulift.{u + 1, u + 1}
        (X := StableCompletion.ZeroComponent R)).symm.toHomotopyEquiv B
  have hm : QuasiIso (LocalCoefficients.pushforwardChainMap
      (LocalCoefficients.UniverseLift.map.{u, u + 1, u + 1}
        (StableCompletion.stableZeroMap R)) B) := by
    exact LocalCoefficients.pushforwardChainMap_quasiIso_comp
      (stableZeroLiftMap R) (LocalCoefficients.UniverseLift.up.{u + 1, u + 1} _) B
      (stableZeroLiftMap_localCoefficients_quasiIso R _) hup
  unfold LocalCoefficients.UniverseLift.chainMap
  infer_instance

/-- The isomorphism is induced by that same original arbitrary-universe chain map. -/
theorem stableZeroMap_localHomology_isIso
    (A : LocalCoefficients.System.{u + 1, u + 1} (StableCompletion.ZeroComponent R)) (n : ℕ) :
    IsIso (LocalCoefficients.UniverseLift.homologyMap.{u, u + 1, u + 1}
      (StableCompletion.stableZeroMap R) A n) := by
  have := stableZeroMap_localCoefficients_quasiIso R A
  change IsIso (HomologicalComplex.homologyMap
    (LocalCoefficients.UniverseLift.chainMap.{u, u + 1, u + 1}
      (StableCompletion.stableZeroMap R) A) n)
  infer_instance

end ModuleCat.FiniteProjective.StableFreeRight
