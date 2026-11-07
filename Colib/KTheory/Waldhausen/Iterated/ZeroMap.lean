/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Iterated.ExactCoherence
public import Colib.Topology.Prespectrum.HomotopyLoop

/-! Literal zero maps and their canonical normalization homotopy for the actual S-prespectrum. -/
/-! Implementation provenance:
`Quillen/Waldhausen/SConstruction/Iterated/ZeroMap.lean` at Quillen
commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, complete
based tracks, signed degrees, hypotheses and independent universes are retained.
The small source is the native `WideSubcategory preservesZero` on
`SmallWaldhausenCategory`, with the existing `AsSmall` transport. -/
@[expose] public section


noncomputable section
open Topology SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor
open scoped Simplicial Topology unitInterval
universe u
namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory

/-- The actual constant-zero model functor gives the literal zero prespectrum map. -/
theorem prespectrumMap_zeroHom (V W : WideSubcategory preservesZero.{u}) :
    prespectrumMap (zeroHom V W) = LoopPrespectrum.zeroHom (prespectrum V) (prespectrum W) := by
  apply LoopPrespectrum.Hom.ext
  funext n
  cases n with
  | zero =>
    apply ContinuousMap.ext
    intro γ
    change Path (stagePoint 0 V) (stagePoint 0 V) at γ
    apply Path.ext
    funext t
    change SSet.toTop.map ((stages 0).map (zeroHom V W)) (γ t) = stagePoint 0 W
    rw [stages_map_zeroHom]
    exact realization_const_apply _ _
  | succ n =>
    apply ContinuousMap.ext
    intro x
    change SSet.toTop.map ((stages n).map (zeroHom V W)) x = stagePoint n W
    rw [stages_map_zeroHom]
    exact realization_const_apply _ _

section Original
universe v
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) (V : Structure D)

theorem asSmallCategoryMap_zeroFunctor :
    asSmallCategoryMap W V (zeroFunctor_isExact W V) rfl =
      zeroHom (asSmallCategory W) (asSmallCategory V) := by
  apply WideSubcategory.hom_ext
  apply SmallWaldhausenCategory.Hom.ext
  rfl

/-- Original zero-preserving constant functors are actual zero spectrum maps. -/
theorem originalPrespectrumMap_zeroFunctor :
    originalPrespectrumMap W V (zeroFunctor_isExact W V) rfl =
      LoopPrespectrum.zeroHom (originalPrespectrum W) (originalPrespectrum V) := by
  change prespectrumMap (asSmallCategoryMap W V (zeroFunctor_isExact W V) rfl) = _
  rw [asSmallCategoryMap_zeroFunctor, prespectrumMap_zeroHom]
  rfl

/-- Canonical normalization of the zero functor has a specified whole based
homotopy to the actual zero prespectrum map. -/
def exactOriginalPrespectrumMapZeroFunctorHomotopy :
    LoopPrespectrum.Homotopy (exactOriginalPrespectrumMap W V (zeroFunctor_isExact W V))
      (LoopPrespectrum.zeroHom (originalPrespectrum W) (originalPrespectrum V)) := by
  let h := zeroFunctor_isExact W V
  let e := (CategoryTheory.rebaseFunctorIso (zeroFunctor V) W.zero V.zero
    ((h.zero W.isZero).iso V.isZero)).symm
  have H := originalPrespectrumTransformationHomotopy W V h.rebase h
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _) rfl e.hom (fun _ ↦ V.weq_iso _ inferInstance)
  simpa only [exactOriginalPrespectrumMap, originalPrespectrumMap_zeroFunctor] using H

end Original
end CategoryTheory.Waldhausen.IteratedS
