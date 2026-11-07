/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.LoopPrefixGroups

/-!
Implementation provenance:
`Quillen/Topology/HomotopyFiber/BasedHomotopySquareMap.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Homotopy-square maps with the original specified target basepoint -/
@[expose] public section
noncomputable section
open scoped Topology
universe u v u' v'
namespace Topology.HomotopyFiber
variable {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'}
  [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace X'] [TopologicalSpace Y']

/-- Equal structure maps induce a fiber map that preserves both actual coordinates. -/
def mapEqMap {f g : C(X, Y)} (h : f = g) (y : Y) :
    C(HomotopyFiber f y, HomotopyFiber g y) where
  toFun p := ⟨p.val, p.property.1.trans (ContinuousMap.congr_fun h p.val.1), p.property.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- An equality of basepoints changes no source coordinate or stored path. -/
def baseEqMap (f : C(X, Y)) {y z : Y} (h : y = z) :
    C(HomotopyFiber f y, HomotopyFiber f z) where
  toFun p := ⟨p.val, p.property.1, p.property.2.trans h⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The actual square map with the specified target basepoint and unchanged stored path. -/
def basedHomotopySquareMap {f : C(X, Y)} {f' : C(X', Y')}
    (u : C(X, X')) (v : C(Y, Y')) (H : (v.comp f).Homotopy (f'.comp u))
    (y : Y) (z : Y') (h : v y = z) :
    C(HomotopyFiber f y, HomotopyFiber f' z) :=
  (baseEqMap f' h).comp (homotopySquareMap u v H y)

/-- The original square track followed by the mapped source path, with endpoint equality only. -/
def basedSquarePrefix {f : C(X, Y)} {f' : C(X', Y')}
    (u : C(X, X')) (v : C(Y, Y')) (H : (v.comp f).Homotopy (f'.comp u))
    (x : X) (y : Y) (z : Y') (h : v y = z) (γ : Path (f x) y) :
    Path (f' (u x)) z :=
  ((H.evalAt x).symm.trans (γ.map v.continuous)).cast rfl h.symm

/-- Corrected inverse naturality retains the specified target basepoint without a new path. -/
theorem loopInverse_basedHomotopySquare_pi [ContractibleSpace X] [ContractibleSpace X']
    {f : C(X, Y)} {f' : C(X', Y')}
    (u : C(X, X')) (v : C(Y, Y')) (H : (v.comp f).Homotopy (f'.comp u))
    (x : X) (y : Y) (z : Y') (h : v y = z) (γ : Path (f x) y) (n : ℕ)
    (b : HomotopyGroup.Pi n (HomotopyFiber f y) (pointWithPath f x y γ)) :
    HomotopyGroup.map (basedLoopMap v h) (basedLoopMap_refl v h)
      (pathTransport (loopEquivOfContractibleSourcePathInverseBasepointPath f x y γ) n
        (HomotopyGroup.map (loopEquivOfContractibleSourcePath f x y γ).invFun rfl b)) =
    pathTransport (loopEquivOfContractibleSourcePathInverseBasepointPath f' (u x) z
      (basedSquarePrefix u v H x y z h γ)) n
      (HomotopyGroup.map (loopEquivOfContractibleSourcePath f' (u x) z
        (basedSquarePrefix u v H x y z h γ)).invFun rfl
          (HomotopyGroup.map (basedHomotopySquareMap u v H y z h) rfl b)) := by
  subst z
  exact loopInverse_homotopySquare_pi u v H x y γ n b

end Topology.HomotopyFiber
