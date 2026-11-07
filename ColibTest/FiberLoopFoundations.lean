/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.Topology.Homotopy.Equiv.HomotopySquare
import Colib.Topology.Homotopy.HomotopyGroup.FundamentalGroup
import Colib.Topology.Homotopy.HomotopyGroup.Loop.Reversal
import Colib.Topology.Homotopy.HomotopyGroup.MovingBasepoint
import Colib.Topology.Homotopy.HomotopyGroup.PathComponent
import Colib.Topology.Homotopy.HomotopyGroup.PathComponentPositive
import Colib.Topology.Homotopy.HomotopyGroup.PathTransportFundamentalGroup
import Colib.Topology.Homotopy.HomotopyGroup.PathTransportGroup
import Colib.Topology.Homotopy.HomotopyGroup.PathTransportHomotopy
import Colib.Topology.Homotopy.HomotopyGroup.ZeroPointClass
import Colib.Topology.HomotopyFiber.ContractibleSourcePath
import Colib.Topology.HomotopyFiber.LoopCentrality

/-! In-package regression tests for the original path-space fiber, specified basepoint
tracks, component inclusion, and the coordinate-zero reversal sign. -/

noncomputable section

open Topology Topology.HomotopyFiber
open scoped unitInterval

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable (f : C(X, Y)) (x : X) (y : Y)

example [ContractibleSpace X] (γ : Path (f x) y) (δ : Path y y) :
    ((loopEquivOfContractibleSourcePath f x y γ) δ).1.2 =
      (γ.trans δ).toContinuousMap :=
  loopEquivOfContractibleSourcePath_path f x y γ δ

example [ContractibleSpace X] (γ : Path (f x) y) :
    Path ((loopEquivOfContractibleSourcePath f x y γ).invFun (pointWithPath f x y γ))
      (Path.refl y) :=
  loopEquivOfContractibleSourcePathInverseBasepointPath f x y γ

example (h : f x = y) :
    (HomotopyGroup.piMap 0 (projection f y) (projection_basepoint f y x h)).ker ≤
      Subgroup.center (HomotopyGroup.Pi 1 (HomotopyFiber f y) (basepoint f y x h)) :=
  ker_piOne_projection_le_center f y x h

example (n : ℕ) :
    (pathComponentPiMulEquiv x n).toMonoidHom = HomotopyGroup.piMap n
      (pathComponentInclusion x) (x := ⟨x, mem_pathComponent_self x⟩) rfl := rfl

example {z : X} (γ : Path x z) (n : ℕ) (a : HomotopyGroup.Pi (n + 1) X x) :
    pathTransportMulEquiv γ n a = pathTransport γ (n + 1) a := rfl

example (n : ℕ) (a : HomotopyGroup.Pi (n + 1) X x) :
    HomotopyGroup.map loopReversal loopReversal_refl (loopShiftEquiv n a) =
      loopShiftEquiv n a⁻¹ :=
  homotopyGroupMap_loopReversal_loopShiftEquiv n a

example (a : HomotopyGroup.Pi 0 (Path x x) (Path.refl x)) :
    (loopShiftEquiv (x := x) 0).symm
      (HomotopyGroup.map loopReversal loopReversal_refl a) =
      ((loopShiftEquiv (x := x) 0).symm a)⁻¹ :=
  loopShiftEquiv_symm_loopReversal 0 a

example {z : X} (p q : Path x z) (h : p.Homotopic q) (n : ℕ) :
    pathTransport p n = pathTransport q n := pathTransport_eq_of_homotopic h n

example {z : X} (p : Path x z) (n : ℕ) (a : HomotopyGroup.Pi n X x) :
    pathTransport p.symm n (pathTransport p n a) = a := pathTransport_symm_apply p n a

example {g : C(X, Y)} (H : f.Homotopy g) (n : ℕ) (a : HomotopyGroup.Pi n X x) :
    pathTransport (H.evalAt x) n (HomotopyGroup.map f rfl a) =
      HomotopyGroup.map g rfl a := pathTransport_homotopyGroupMap_homotopy H x n a

example {g : C(X, Y)} (H : f.Homotopy g) {y₀ y₁ : Y}
    (hf : f x = y₀) (hg : g x = y₁) (n : ℕ) (a : HomotopyGroup.Pi n X x) :
    pathTransport ((H.evalAt x).cast hf.symm hg.symm) n (HomotopyGroup.map f hf a) =
      HomotopyGroup.map g hg a :=
  pathTransport_homotopyGroupMap_homotopy_cast H x hf hg n a

example (h : f x = y) (a : HomotopyGroup.Pi 1 X x) :
    HomotopyGroup.pi1MulEquivFundamentalGroup (HomotopyGroup.piMap 0 f h a) =
      FundamentalGroup.mapOfEq f h (HomotopyGroup.pi1MulEquivFundamentalGroup a) :=
  HomotopyGroup.pi1MulEquivFundamentalGroup_naturality f h a

example {z : X} (γ : Path x z) (a : HomotopyGroup.Pi 1 X x) :
    HomotopyGroup.pi1MulEquivFundamentalGroup (pathTransport γ 1 a) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath γ
        (HomotopyGroup.pi1MulEquivFundamentalGroup a) :=
  piOneEquivFundamentalGroup_pathTransport γ a

example {g : C(X, Y)} (H : f.Homotopy g) (γ : Path (f x) y) (δ : Path (g x) y)
    (hc : ∀ a b : HomotopyGroup.Pi 1 Y y, a * b = b * a) :
    (pathTransportMulEquiv γ 0).toMonoidHom.comp (HomotopyGroup.piMap 0 f rfl) =
      (pathTransportMulEquiv δ 0).toMonoidHom.comp (HomotopyGroup.piMap 0 g rfl) :=
  piOne_homotopy_corrected H γ δ hc

example (h : f x = y) (z : X) :
    HomotopyGroup.map f h (zeroPointClass x z) = zeroPointClass y (f z) := rfl

example : (pathComponentFundamentalGroupEquiv x).toMonoidHom = FundamentalGroup.map
    (⟨Subtype.val, continuous_subtype_val⟩ : C(pathComponent x, X))
    ⟨x, mem_pathComponent_self x⟩ := rfl

example (e : ContinuousMap.HomotopyEquiv X Y) (h : f.Homotopic e.toFun) :
    (e.ofHomotopic f h).toFun = f := rfl
