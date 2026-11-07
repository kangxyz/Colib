/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Waldhausen.Fibration.SpectrumComparison
public import Colib.Topology.HomotopyFiber.BasedLESNaturality

/-!
# The original change-of-weak boundary at spectrum level one

The actual small-model homeomorphisms and whole canonical fiber comparison
preserve the original geometric connecting homomorphism at level one.
This does not identify it with the signed stable connecting homomorphism;
that comparison additionally requires the structure-map coordinate sign.
-/
/-! Implementation provenance:
`Quillen/Waldhausen/Fibration/LevelOneConnectingComparison.lean` at Quillen
commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, complete
based tracks, signed degrees, hypotheses and independent universes are retained.
The small source is the native `WideSubcategory preservesZero` on
`SmallWaldhausenCategory`, with the existing `AsSmall` transport. -/
@[expose] public section
noncomputable section
open Topology SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology
universe u v
namespace CategoryTheory.Waldhausen.Fibration
open IteratedS LoopPrespectrum
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V)

/-- The actual fiber homeomorphism is the based map of its original strict square. -/
theorem originalFiberToSpectrumLevelOne_mapAt :
    (originalFiberToSpectrumLevelOne N).toHomotopyEquiv.toFun =
      HomotopyFiber.mapAt (p := changeWeakMap N) (q := (changeWeakPrespectrumMap N).map 1)
        V.asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun
        N.coarse.asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun
        (asSmallDeloopingHomeomorph_naturality (changeWeak_exact N))
        N.coarse.kBasepoint ((originalPrespectrum N.coarse).point 1)
        N.coarse.asSmallDeloopingHomeomorph_basepoint := by
  ext z
  apply Subtype.ext
  rfl

/-- Both chosen zero points are retained by the original whole-path fiber homeomorphism. -/
theorem originalFiberToSpectrumLevelOne_basepoint :
    originalFiberToSpectrumLevelOne N
        (HomotopyFiber.basepoint (changeWeakMap N) N.coarse.kBasepoint
          V.kBasepoint (changeWeakMap_basepoint N)) =
      (homotopyFiber (changeWeakPrespectrumMap N)).point 1 := by
  apply Subtype.ext
  apply Prod.ext
  · exact V.asSmallDeloopingHomeomorph_basepoint
  · apply ContinuousMap.ext
    intro t
    exact N.coarse.asSmallDeloopingHomeomorph_basepoint

/-- The original canonical fiber K-map is exactly the specified level-one spectrum comparison. -/
theorem originalFiberToSpectrumLevelOne_canonicalFiberKMap (n : ℕ) :
    (HomotopyGroup.piMap n (originalFiberToSpectrumLevelOne N).toHomotopyEquiv.toFun
        (originalFiberToSpectrumLevelOne_basepoint N)).comp (canonicalFiberKMap N n) =
      (HomotopyGroup.piMap n ((canonicalFiberPrespectrumMap N).map 1)
        ((canonicalFiberPrespectrumMap N).map_point 1)).comp
          ((acyclicStructure N).asSmallKEquiv n).toMonoidHom := by
  change (HomotopyGroup.piMap n _ _).comp (HomotopyGroup.piMap n _ _) =
    (HomotopyGroup.piMap n _ _).comp (HomotopyGroup.piMap n _ _)
  rw [← HomotopyGroup.mapHom_comp, ← HomotopyGroup.mapHom_comp]
  congr 1
  exact canonicalFiberPrespectrumMap_level_one_square N

/-- The original fiber homeomorphism preserves the geometric boundary with its based points. -/
theorem originalFiberToSpectrumLevelOne_connecting (n : ℕ) :
    (HomotopyGroup.piMap n (originalFiberToSpectrumLevelOne N).toHomotopyEquiv.toFun
        (originalFiberToSpectrumLevelOne_basepoint N)).comp
      (HomotopyFiber.connectingHom (changeWeakMap N) N.coarse.kBasepoint V.kBasepoint
        (changeWeakMap_basepoint N) n) =
    (HomotopyFiber.connectingHom ((changeWeakPrespectrumMap N).map 1)
      ((originalPrespectrum N.coarse).point 1) ((originalPrespectrum V).point 1)
      ((changeWeakPrespectrumMap N).map_point 1) n).comp
        (N.coarse.asSmallKEquiv (n + 1)).toMonoidHom := by
  have h := HomotopyFiber.connectingHom_mapAt_natural
    (f := changeWeakMap N) (g := (changeWeakPrespectrumMap N).map 1)
    V.asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun
    N.coarse.asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun
    (asSmallDeloopingHomeomorph_naturality (changeWeak_exact N))
    V.kBasepoint N.coarse.kBasepoint ((originalPrespectrum V).point 1)
    ((originalPrespectrum N.coarse).point 1) (changeWeakMap_basepoint N)
    ((changeWeakPrespectrumMap N).map_point 1)
    V.asSmallDeloopingHomeomorph_basepoint
    N.coarse.asSmallDeloopingHomeomorph_basepoint n
  change (HomotopyGroup.piMap n _ _).comp _ =
    (HomotopyFiber.connectingHom ((changeWeakPrespectrumMap N).map 1)
      ((originalPrespectrum N.coarse).point 1) ((originalPrespectrum V).point 1)
      ((changeWeakPrespectrumMap N).map_point 1) n).comp (HomotopyGroup.piMap (n + 1) _ _)
  simpa only [← originalFiberToSpectrumLevelOne_mapAt] using h

/-- The unchanged original K-boundary agrees with the actual geometric boundary at level one. -/
theorem canonicalFiberPrespectrumMap_levelOne_connecting
    (h : IsWeakHomotopyEquivalence (canonicalFiberMap N)) (n : ℕ)
    (a : N.coarse.K (n + 1)) :
    HomotopyGroup.piMap n ((canonicalFiberPrespectrumMap N).map 1)
        ((canonicalFiberPrespectrumMap N).map_point 1)
      ((acyclicStructure N).asSmallKEquiv n (changeWeakConnectingHom N h n a)) =
    HomotopyFiber.connectingHom ((changeWeakPrespectrumMap N).map 1)
      ((originalPrespectrum N.coarse).point 1) ((originalPrespectrum V).point 1)
      ((changeWeakPrespectrumMap N).map_point 1) n
      (N.coarse.asSmallKEquiv (n + 1) a) := by
  have hs := DFunLike.congr_fun (originalFiberToSpectrumLevelOne_canonicalFiberKMap N n)
    (changeWeakConnectingHom N h n a)
  simp only [MonoidHom.comp_apply] at hs
  exact hs.symm.trans ((congrArg
    (HomotopyGroup.piMap n (originalFiberToSpectrumLevelOne N).toHomotopyEquiv.toFun
      (originalFiberToSpectrumLevelOne_basepoint N))
    (canonicalFiberKMap_connecting N h n a)).trans
      (DFunLike.congr_fun (originalFiberToSpectrumLevelOne_connecting N n) a))

end CategoryTheory.Waldhausen.Fibration
