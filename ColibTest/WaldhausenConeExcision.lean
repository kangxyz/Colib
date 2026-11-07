/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

import Colib.KTheory.Waldhausen.Fibration.ConeComparison

/-!
Regressions for the unchanged cone descent, every cylinder point, the signed stable
boundary, unconditional finite S-model excision and independent object/hom universes.
-/

open CategoryTheory Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.Fibration
open SmallWaldhausenCategory

universe u v

noncomputable section

variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V)

example :
    mappingConeInclusion (acyclicInclusionPrespectrumMap N) ≫ canonicalConePrespectrumMap N =
      changeWeakPrespectrumMap N :=
  canonicalConePrespectrumMap_inclusion N

example (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (acyclicStructure N)).space n) :
    (canonicalConePrespectrumMap N).map n
        (ReducedMappingCone.cylinder ((originalPrespectrum (acyclicStructure N)).point n)
          ((originalPrespectrum V).point n) ((acyclicInclusionPrespectrumMap N).map n) (s, x)) =
      (acyclicPrespectrumNullhomotopy N).level n (s, x) :=
  canonicalConePrespectrumMap_cylinder N n s x

example (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map (canonicalConePrespectrumMap N) ≫
        stableFiberConnecting (changeWeakPrespectrumMap N) d =
      stableMappingConeConnecting (acyclicInclusionPrespectrumMap N)
          (originalPrespectrum_mappingConeFiberComparison_isStableEquivalence _ _ _) d ≫
        (stableHomotopyFunctor d).map (canonicalFiberPrespectrumMap N) :=
  canonicalConePrespectrumMap_connecting N d

example [N.coarse.weq.HasTwoOutOfThreeProperty]
    (he : ExtensionAxiom N.coarse) (D : RowFactorization.JointData N)
    (hs : RowFactorization.SecondEndpointSection N D) :
    IsStableEquivalence (canonicalConePrespectrumMap N) :=
  canonicalConePrespectrumMap_isStableEquivalence_general N he D hs

example {D : Type u} [Category.{v} D] (W : Structure C) (U : Structure D)
    (f : originalPrespectrum W ⟶ originalPrespectrum U) (n : ℕ) :
    IsHomotopyConnectedMap ((mappingConeFiberComparison f).map (n + 1)) (2 * n) :=
  originalPrespectrum_mappingConeFiberComparison_isHomotopyConnectedMap W U f n

example {D : Type u} [Category.{v} D] (W : Structure C) (U : Structure D)
    (f : originalPrespectrum W ⟶ originalPrespectrum U) :
    IsStableEquivalence (mappingConeFiberComparison f) :=
  originalPrespectrum_mappingConeFiberComparison_isStableEquivalence W U f

-- The structure loop retains independent cone and loop coordinates, not just their endpoints.
example {E F : LoopPrespectrum.{u}} (f : E ⟶ F) (n : ℕ)
    (s t : unitInterval) (x : E.space n) :
    (mappingCone f).structureMap n
        (ReducedMappingCone.cylinder (E.point n) (F.point n) (f.map n) (s, x)) t =
      ReducedMappingCone.cylinder (E.point (n + 1)) (F.point (n + 1)) (f.map (n + 1))
        (s, E.structureMap n x t) := rfl
