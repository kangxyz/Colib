/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.SquareEquivalence
public import Colib.Topology.HomotopyFiber.BasepointTransport
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.LeftComponentTranslation
public import Colib.Topology.Homotopy.HomotopyGroup.ZeroPointClass
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransportFundamentalGroup

/-! # Original fiber transport between loop components

The actual left-prefix maps and a displayed source suffix induce a genuine
homotopy equivalence of the original loop-map fibers. The formulas retain
the complete paths and their original order.
-/
/-! Implementation source: `Quillen/Topology/HomotopyFiber/LoopComponentTransport.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, basepoints,
coefficients and signs are retained with native Colib dependencies. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open Topology HomotopyGroup
open scoped Topology
universe u
namespace Topology.HomotopyFiber.LoopComponentTransport

variable {X : Type u} [TopologicalSpace X]

/-- A displayed path identifies the original zero-dimensional point classes. -/
theorem zeroPointClass_eq_of_path (x : X) {z w : X} (p : Path z w) :
    zeroPointClass x z = zeroPointClass x w := by
  apply Quotient.sound
  exact ⟨{
    toFun a := p a.1
    continuous_toFun := p.continuous.comp continuous_fst
    map_zero_left _ := p.source
    map_one_left _ := p.target
    prop' := by rintro t s ⟨i, _⟩; exact Fin.elim0 i }⟩

/-- The original connecting set map evaluates an actual loop as its literal fiber inclusion. -/
theorem connectingMap_path {Y : Type u} [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (y : Y) (h : f x = y) (p : Path y y) :
    HomotopyFiber.connectingMap f y x h 0
      (HomotopyGroup.pi1MulEquivFundamentalGroup.symm ⟦p⟧) =
    zeroPointClass (HomotopyFiber.basepoint f y x h)
      (HomotopyFiber.loopInclusion f y x h p) := by
  rfl

variable {Y : Type u} [TopologicalSpace Y] (f : C(X, Y)) {x : X} {y : Y}
  (h : f x = y) (α : Path x x) (γ : Path y y) (hα : basedLoopMap f h α = γ)

include hα in
/-- The strict square is the original postcomposition of the entire left prefix. -/
theorem prefixSquare :
    (loopLeftTranslationEquiv γ).toFun.comp (basedLoopMap f h) =
      (basedLoopMap f h).comp (loopLeftTranslationEquiv α).toFun :=
  by
  simpa only [hα] using (loopLeftTranslationEquiv_naturality f h α).symm

variable (σ : Path (α.trans (Path.refl x)) α)

/-- The target suffix retains the original source suffix under the same based loop map. -/
def imageSuffix :
    Path (loopLeftTranslationEquiv γ (Path.refl y))
      γ :=
  (σ.map (basedLoopMap f h).continuous).cast (by
    rw [loopLeftTranslationEquiv_apply, basedLoopMap_trans, basedLoopMap_refl, hα]) hα.symm

/-- The actual prefix square and suffix give an equivalence of the original loop-map fibers. -/
def fiberComponentEquiv :
    ContinuousMap.HomotopyEquiv
      (HomotopyFiber (basedLoopMap f h) (Path.refl y))
      (HomotopyFiber (basedLoopMap f h) γ) :=
  (HomotopyFiber.mapHomotopyEquivOfEquivalences (loopLeftTranslationEquiv α)
    (loopLeftTranslationEquiv γ) (prefixSquare f h α γ hα)
    (Path.refl y)).trans
      (HomotopyFiber.basepointTransportEquiv (basedLoopMap f h) (imageSuffix f h α γ hα σ))

/-- The equivalence keeps exactly the prefixed original source loop. -/
theorem fiberComponentEquiv_source
    (z : HomotopyFiber (basedLoopMap f h) (Path.refl y)) :
    (fiberComponentEquiv f h α γ hα σ z).val.1 = α.trans z.val.1 := by
  change loopLeftTranslationEquiv α z.val.1 = _
  exact loopLeftTranslationEquiv_apply α z.val.1

/-- The original fiber path is left-prefixed, then followed by the actual mapped suffix. -/
theorem fiberComponentEquiv_path
    (z : HomotopyFiber (basedLoopMap f h) (Path.refl y)) :
    (fiberComponentEquiv f h α γ hα σ z).val.2 =
      (((HomotopyFiber.toPath (basedLoopMap f h) (Path.refl y) z).map
        (loopLeftTranslationEquiv γ).continuous).trans
          (imageSuffix f h α γ hα σ)).toContinuousMap := by
  rw [fiberComponentEquiv, ContinuousMap.HomotopyEquiv.trans_apply,
    HomotopyFiber.basepointTransportEquiv_path]
  rfl

/-- Conjugation by the same mapped suffix gives the actual loop in the new component. -/
def componentLoop (β : Path (Path.refl y) (Path.refl y)) :
    Path γ γ :=
  (imageSuffix f h α γ hα σ).symm.trans
    ((β.map (loopLeftTranslationEquiv γ).continuous).trans
      (imageSuffix f h α γ hα σ))

/-- The translated inclusion has the original source suffix as a return path. -/
def componentLoopIterated (β : Path (Path.refl y) (Path.refl y)) :
    HomotopyFiber.IteratedFiber (basedLoopMap f h) γ α := by
  refine ⟨(fiberComponentEquiv f h α γ hα σ
    (HomotopyFiber.loopInclusion (basedLoopMap f h) (Path.refl y) (Path.refl x)
      (basedLoopMap_refl f h) β), σ.toContinuousMap), ?_, σ.target⟩
  exact σ.source.trans (fiberComponentEquiv_source f h α γ hα σ
    (HomotopyFiber.loopInclusion (basedLoopMap f h) (Path.refl y) (Path.refl x)
      (basedLoopMap_refl f h) β)).symm

/-- The original iterated-fiber map gives precisely the conjugated component loop. -/
theorem componentLoopIterated_toLoops (β : Path (Path.refl y) (Path.refl y)) :
    HomotopyFiber.iteratedToLoops (basedLoopMap f h) γ α hα
      (componentLoopIterated f h α γ hα σ β) = componentLoop f h α γ hα σ β := by
  apply Path.ext
  funext t
  dsimp only [HomotopyFiber.iteratedToLoops, ContinuousMap.coe_mk]
  rw [Path.trans_apply, componentLoop, Path.trans_apply]
  split_ifs
  · rfl
  · change (fiberComponentEquiv f h α γ hα σ _).val.2 _ = _
    rw [fiberComponentEquiv_path]
    rfl

/-- The original iterated-fiber deformation connects the actual two displayed points. -/
def componentLoopFiberPath (β : Path (Path.refl y) (Path.refl y)) :
    Path
      (HomotopyFiber.loopInclusion (basedLoopMap f h) γ α hα
        (componentLoop f h α γ hα σ β))
      (fiberComponentEquiv f h α γ hα σ
        (HomotopyFiber.loopInclusion (basedLoopMap f h) (Path.refl y) (Path.refl x)
          (basedLoopMap_refl f h) β)) := by
  let H := HomotopyFiber.iteratedLeftInverseHomotopy
    (basedLoopMap f h) γ α hα
  let z := componentLoopIterated f h α γ hα σ β
  refine ⟨(HomotopyFiber.projection
    (HomotopyFiber.projection (basedLoopMap f h) γ) α).comp
    (H.toHomotopy.evalAt z).toContinuousMap, ?_, ?_⟩
  · change (H (0, z)).val.1 = _
    rw [H.apply_zero]
    change HomotopyFiber.loopInclusion _ _ _ _
      (HomotopyFiber.iteratedToLoops _ _ _ _ z) = _
    rw [componentLoopIterated_toLoops]
  · change (H (1, z)).val.1 = _
    rw [H.apply_one]
    rfl

/-- The corrected component map carries a loop class to the displayed conjugate. -/
theorem componentLoop_class (β : Path (Path.refl y) (Path.refl y)) :
    HomotopyGroup.pi1MulEquivFundamentalGroup
      (pathTransport (imageSuffix f h α γ hα σ) 1
        (HomotopyGroup.map (loopLeftTranslationEquiv γ).toFun rfl
          (HomotopyGroup.pi1MulEquivFundamentalGroup.symm ⟦β⟧))) =
      ⟦componentLoop f h α γ hα σ β⟧ := by
  rw [piOneEquivFundamentalGroup_pathTransport]
  rw [HomotopyGroup.pi1MulEquivFundamentalGroup_naturality, MulEquiv.apply_symm_apply,
    FundamentalGroup.mapOfEq_apply]
  simp only [Path.Homotopic.Quotient.cast_rfl_rfl]
  rfl

end Topology.HomotopyFiber.LoopComponentTransport
