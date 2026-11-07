/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.BasedHomotopySquareMap
public import Colib.Topology.HomotopyFiber.LoopPrefixBasepointNaturality

/-!
Implementation provenance:
`Quillen/Topology/HomotopyFiber/LoopComparisonNaturality.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Based naturality of the original inverse comparisons from an actual fiber square -/
@[expose] public section
noncomputable section
open scoped Topology
universe u v u' v' w w'
namespace Topology.HomotopyFiber
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'}
  {A : Type w} {A' : Type w'}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
  [TopologicalSpace A] [TopologicalSpace A']

/-- An actual square of fiber comparisons induces the corrected naturality square of the
unchanged inverse loop comparisons. Every source and target basepoint path is displayed. -/
theorem loopComparison_naturality_pi [ContractibleSpace X] [ContractibleSpace X']
    {f : C(X, Y)} {f' : C(X', Y')}
    (u : C(X, X')) (v : C(Y, Y')) (H : (v.comp f).Homotopy (f'.comp u))
    (y : Y) (z : Y') (h : v y = z)
    (c : C(A, HomotopyFiber f y)) (d : C(A', HomotopyFiber f' z)) (a : C(A, A'))
    (J : ((basedHomotopySquareMap u v H y z h).comp c).Homotopy (d.comp a))
    (x : A) (x' : A') (p : Path (a x) x') (n : ℕ) (b : HomotopyGroup.Pi n A x) :
    HomotopyGroup.map (basedLoopMap v h) (basedLoopMap_refl v h)
      (pathTransport (loopEquivOfContractibleSourcePathInverseBasepointPath
        f (c x).val.1 y (toPath f y (c x))) n
        (HomotopyGroup.map (loopEquivOfContractibleSourcePath f (c x).val.1 y
          (toPath f y (c x))).invFun rfl (HomotopyGroup.map c rfl b))) =
    pathTransport (loopEquivOfContractibleSourcePathInverseBasepointPath
      f' (d x').val.1 z (toPath f' z (d x'))) n
      (HomotopyGroup.map (loopEquivOfContractibleSourcePath f' (d x').val.1 z
        (toPath f' z (d x'))).invFun rfl
        (HomotopyGroup.map d rfl (pathTransport p n (HomotopyGroup.map a rfl b)))) := by
  let M := basedHomotopySquareMap u v H y z h
  let q : Path (M (c x)) (d x') := (J.evalAt x).trans (p.map d.continuous)
  have ht : pathTransport q n (HomotopyGroup.map M rfl (HomotopyGroup.map c rfl b)) =
      HomotopyGroup.map d rfl (pathTransport p n (HomotopyGroup.map a rfl b)) := by
    rw [pathTransport_trans]
    rw [← HomotopyGroup.map_comp c rfl M rfl]
    dsimp only [M]
    exact (congrArg (pathTransport (p.map d.continuous) n)
      (pathTransport_homotopyGroupMap_homotopy J x n b)).trans
      ((congrArg (pathTransport (p.map d.continuous) n)
        (HomotopyGroup.map_comp a rfl d rfl b)).trans
          (pathTransport_naturality d p n (HomotopyGroup.map a rfl b)))
  have hs := loopInverse_basedHomotopySquare_pi u v H (c x).val.1 y z h
    (toPath f y (c x)) n (HomotopyGroup.map c rfl b)
  have hq := loopInverse_pathTransport_pi q n
    (HomotopyGroup.map M rfl (HomotopyGroup.map c rfl b))
  rw [ht] at hq
  exact hs.trans hq

end Topology.HomotopyFiber
