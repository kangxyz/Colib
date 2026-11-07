/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.OmegaConnectivity
public import Colib.KTheory.Waldhausen.Iterated.OmegaSpectrum

/-!
# Finite connectivity growth for the original iterated-S prespectrum

The actually proved Omega structure and connected realized S-stages discharge all connectivity
assumptions. At the original level `n+1`, all homotopy sets through degree `n` vanish at every
point. The original map to a point is `n+1`-connected, and every map between original S-models
is `n`-connected there. These are genuine finite fiber bounds, not merely a stable assertion.
-/
/-! Implementation provenance: `Quillen/Waldhausen/SConstruction/Iterated/FiniteConnectivity.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original maps, full null track, degree bounds, signed boundary and independent
object/hom universes are retained using the native strict chosen-zero subcategory. -/
@[expose] public section
noncomputable section
open CategoryTheory Topology.LoopPrespectrum
universe u v
namespace CategoryTheory.Waldhausen.IteratedS
open Topology SmallWaldhausenCategory

/-- All points of the literal positive S-level have the required finite homotopy-set vanishing. -/
theorem prespectrum_positiveLevel_homotopyGroup_subsingleton_at
    (W : WideSubcategory preservesZero.{u})
    (n k : ℕ) (hk : k ≤ n) (x : (prespectrum W).space (n + 1)) :
    Subsingleton (HomotopyGroup.Pi k ((prespectrum W).space (n + 1)) x) :=
  positiveLevel_homotopyGroup_subsingleton_at (prespectrum W) (prespectrum_isOmega W)
    (fun r ↦ stageSpace_pathConnected r W) n k hk x

/-- The literal original S-level map to a point has an unconditional growing fiber bound. -/
theorem prespectrum_positiveLevel_toPoint_isHomotopyConnectedMap
    (W : WideSubcategory preservesZero.{u}) (n : ℕ) :
    IsHomotopyConnectedMap
      (ContinuousMap.const ((prespectrum W).space (n + 1)) (PUnit.unit : PUnit.{u + 1}))
      (n + 1) :=
  positiveLevel_toPoint_isHomotopyConnectedMap (prespectrum W) (prespectrum_isOmega W)
    (fun r ↦ stageSpace_pathConnected r W) n

/-- Every unchanged map between actual S-models is finitely connected in the required range. -/
theorem prespectrum_positiveLevel_isHomotopyConnectedMap {W V : WideSubcategory preservesZero.{u}}
    (f : prespectrum W ⟶ prespectrum V) (n : ℕ) :
    IsHomotopyConnectedMap (f.map (n + 1)) n :=
  positiveLevel_isHomotopyConnectedMap f (prespectrum_isOmega W) (prespectrum_isOmega V)
    (fun r ↦ stageSpace_pathConnected r W) (fun r ↦ stageSpace_pathConnected r V) n

/-- The original independently-universed model retains the same all-point vanishing bound. -/
theorem originalPrespectrum_positiveLevel_homotopyGroup_subsingleton_at
    {C : Type u} [Category.{v} C] (W : Structure C) (n k : ℕ) (hk : k ≤ n)
    (x : (originalPrespectrum W).space (n + 1)) :
    Subsingleton (HomotopyGroup.Pi k ((originalPrespectrum W).space (n + 1)) x) :=
  prespectrum_positiveLevel_homotopyGroup_subsingleton_at (asSmallCategory W) n k hk x

/-- The point-map growth uses the actual original small-model universe, without a new point. -/
theorem originalPrespectrum_positiveLevel_toPoint_isHomotopyConnectedMap
    {C : Type u} [Category.{v} C] (W : Structure C) (n : ℕ) :
    IsHomotopyConnectedMap
      (ContinuousMap.const ((originalPrespectrum W).space (n + 1))
        (PUnit.unit : PUnit.{max u v + 1})) (n + 1) :=
  prespectrum_positiveLevel_toPoint_isHomotopyConnectedMap (asSmallCategory W) n

/-- Original prespectrum maps have the growing finite bound with no added connectivity premise. -/
theorem originalPrespectrum_positiveLevel_isHomotopyConnectedMap
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (W : Structure C) (V : Structure D) (f : originalPrespectrum W ⟶ originalPrespectrum V)
    (n : ℕ) : IsHomotopyConnectedMap (f.map (n + 1)) n :=
  prespectrum_positiveLevel_isHomotopyConnectedMap f n

end CategoryTheory.Waldhausen.IteratedS
