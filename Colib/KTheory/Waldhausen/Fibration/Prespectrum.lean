/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Iterated.ZeroMap
public import Colib.KTheory.Waldhausen.Fibration.CanonicalFiberMap
public import Colib.Topology.Prespectrum.HomotopyFiber

/-!
The actual acyclic inclusion, change of weaknesses and specified coherent fiber lift. No stable
equivalence is asserted by this construction.
-/
/-! Implementation provenance:
`Quillen/Waldhausen/Fibration/Prespectrum.lean` at Quillen
commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, complete
based tracks, signed degrees, hypotheses and independent universes are retained.
The small source is the native `WideSubcategory preservesZero` on
`SmallWaldhausenCategory`, with the existing `AsSmall` transport. -/
@[expose] public section

open CategoryTheory.Waldhausen.IteratedS



noncomputable section
open Topology SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u v
namespace CategoryTheory.Waldhausen.Fibration
open IteratedS
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V)

/-- The original change of weak equivalences on every actual S-spectrum stage. -/
def changeWeakPrespectrumMap : originalPrespectrum V ⟶ originalPrespectrum N.coarse :=
  originalPrespectrumMap V N.coarse (changeWeak_exact N) N.zero_eq.symm

/-- The original acyclic inclusion on every actual S-spectrum stage. -/
def acyclicInclusionPrespectrumMap :
    originalPrespectrum (acyclicStructure N) ⟶ originalPrespectrum V :=
  originalPrespectrumMap (acyclicStructure N) V (acyclicInclusion_exact N) rfl

/-- The actual zero-to-acyclic transformation gives the specified whole based
nullhomotopy of the original spectrum composite, with no fibration premise. -/
def acyclicPrespectrumNullhomotopy : LoopPrespectrum.Homotopy
    (acyclicInclusionPrespectrumMap N ≫ changeWeakPrespectrumMap N)
    (LoopPrespectrum.zeroHom (originalPrespectrum (acyclicStructure N))
      (originalPrespectrum N.coarse)) := by
  have H := (originalPrespectrumTransformationHomotopy (acyclicStructure N) N.coarse
    (zeroFunctor_isExact _ _) (acyclicInclusion_coarse_exact N) rfl
    (by simpa only [acyclicInclusion_zero] using N.coarse_zero.symm) (zeroToAcyclicInclusion N)
    (zeroToAcyclicInclusion_weak N)).symm
  have he : originalPrespectrumMap (acyclicStructure N) N.coarse
      (acyclicInclusion_coarse_exact N) (by simpa only [acyclicInclusion_zero] using
        N.coarse_zero.symm) =
      acyclicInclusionPrespectrumMap N ≫ changeWeakPrespectrumMap N := by
    exact originalPrespectrumMap_comp (acyclicStructure N) V N.coarse
      (acyclicInclusion_exact N) (changeWeak_exact N) rfl N.zero_eq.symm
  exact {
    level := H.level
    at_zero n x := (H.at_zero n x).trans (congrArg (fun f ↦ f.map n x) he)
    at_one n x := (H.at_one n x).trans
      (congrArg (fun f ↦ f.map n x) (originalPrespectrumMap_zeroFunctor (acyclicStructure N)
        N.coarse))
    at_point := H.at_point
    comm := H.comm }

/-- The specified original nullhomotopy defines an actual map into the
path-space fiber spectrum; no weak equivalence is assumed in this construction. -/
def canonicalFiberPrespectrumMap : originalPrespectrum (acyclicStructure N) ⟶
    LoopPrespectrum.homotopyFiber (changeWeakPrespectrumMap N) :=
  LoopPrespectrum.homotopyFiberLift (changeWeakPrespectrumMap N)
    (acyclicInclusionPrespectrumMap N) (acyclicPrespectrumNullhomotopy N)

@[simp] theorem canonicalFiberPrespectrumMap_source (n : ℕ)
    (x : (originalPrespectrum (acyclicStructure N)).space n) :
    ((canonicalFiberPrespectrumMap N).map n x).1.1 =
      (acyclicInclusionPrespectrumMap N).map n x := rfl

@[simp] theorem canonicalFiberPrespectrumMap_path (n : ℕ)
    (x : (originalPrespectrum (acyclicStructure N)).space n) (s : unitInterval) :
    ((canonicalFiberPrespectrumMap N).map n x).1.2 s =
      (acyclicPrespectrumNullhomotopy N).level n (s,x) := rfl

@[simp] theorem canonicalFiberPrespectrumMap_projection :
    canonicalFiberPrespectrumMap N ≫
      LoopPrespectrum.homotopyFiberProjection (changeWeakPrespectrumMap N) =
      acyclicInclusionPrespectrumMap N :=
  LoopPrespectrum.homotopyFiberLift_projection _ _ _

end CategoryTheory.Waldhausen.Fibration
