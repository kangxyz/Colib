/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.LoopPrefixUnitCoherence
public import Colib.Topology.HomotopyFiber.ContractibleSourcePathGroups
public import Colib.Topology.Homotopy.HomotopyGroup.BasedMapNaturality

/-!
Implementation provenance:
`Quillen/Topology/HomotopyFiber/LoopPrefixGroups.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Corrected naturality of the original loop and fiber maps -/
@[expose] public section
noncomputable section
open scoped Topology
universe u v u' v'
namespace Topology.HomotopyFiber
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'}
  [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace X'] [TopologicalSpace Y']

/-- The contraction-independent forward square commutes on every original homotopy set,
with its actual unit paths retained. -/
theorem loopPrefix_homotopySquare_pi {f : C(X, Y)} {f' : C(X', Y')}
    (u : C(X, X')) (v : C(Y, Y')) (H : (v.comp f).Homotopy (f'.comp u))
    (x : X) (y : Y) (γ : Path (f x) y) (n : ℕ)
    (a : HomotopyGroup.Pi n (Path y y) (Path.refl y)) :
    pathTransport (loopPrefixUnitPath f' (u x) (v y)
      ((H.evalAt x).symm.trans (γ.map v.continuous))) n
      (HomotopyGroup.map (loopPrefix f' (u x) (v y)
        ((H.evalAt x).symm.trans (γ.map v.continuous))) rfl
          (HomotopyGroup.map (basedLoopMap v rfl) rfl a)) =
      HomotopyGroup.map (homotopySquareMap u v H y) rfl
        (pathTransport (loopPrefixUnitPath f x y γ) n
          (HomotopyGroup.map (loopPrefix f x y γ) rfl a)) := by
  let L := loopPrefixHomotopySquare u v H x y γ
  let P := loopPrefixUnitPath f x y γ
  let Q := loopPrefixUnitPath f' (u x) (v y)
    ((H.evalAt x).symm.trans (γ.map v.continuous))
  let M := homotopySquareMap u v H y
  have hc : ((Path.refl _).trans Q).Homotopic
      ((L.evalAt (Path.refl y)).trans ((P.map M.continuous).trans (Path.refl _))) :=
    (Path.Homotopic.refl_trans Q).trans
      ((show Q.Homotopic ((L.evalAt (Path.refl y)).trans (P.map M.continuous)) from
        ⟨loopPrefixHomotopySquareUnitCoherence u v H x y γ⟩).trans
          ((Path.Homotopic.refl _).hcomp (Path.Homotopic.trans_refl _).symm))
  have hh := homotopyGroupMap_based_square (basedLoopMap v rfl) M
      (loopPrefix f x y γ)
      (loopPrefix f' (u x) (v y) ((H.evalAt x).symm.trans (γ.map v.continuous))) L
      (Path.refl y) (pointWithPath f x y γ) (Path.refl (v y))
      (pointWithPath f' (u x) (v y) ((H.evalAt x).symm.trans (γ.map v.continuous)))
      (Path.refl _) (Path.refl _) P Q hc n a
  convert hh using 1 <;> simp only [pathTransport_refl] <;> rfl

private theorem correctedMap_congr {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {f g : C(A, B)} (h : f = g) (x : A) (y : B)
    (p : Path (f x) y) (q : Path (g x) y) (hpq : ∀ t, p t = q t)
    (n : ℕ) (a : HomotopyGroup.Pi n A x) :
    pathTransport p n (HomotopyGroup.map f rfl a) =
      pathTransport q n (HomotopyGroup.map g rfl a) := by
  subst g
  have he : p = q := Path.ext (funext hpq)
  subst q
  rfl

/-- The explicit prefix and the original equivalence induce exactly the same corrected map. -/
theorem loopPrefix_corrected_pi [ContractibleSpace X]
    (f : C(X, Y)) (x : X) (y : Y) (γ : Path (f x) y) (n : ℕ)
    (a : HomotopyGroup.Pi n (Path y y) (Path.refl y)) :
    pathTransport (loopPrefixUnitPath f x y γ) n
      (HomotopyGroup.map (loopPrefix f x y γ) rfl a) =
    pathTransport (loopEquivOfContractibleSourcePathUnitPath f x y γ) n
      (HomotopyGroup.map (loopEquivOfContractibleSourcePath f x y γ).toFun rfl a) :=
  correctedMap_congr (loopPrefix_eq_forward f x y γ) _ _ _ _
    (loopPrefixUnitPath_apply f x y γ) n a

/-- Naturality of the existing inverse and its specified based track follows by
cancelling the actual forward maps, without a natural choice of contraction. -/
theorem loopInverse_homotopySquare_pi [ContractibleSpace X] [ContractibleSpace X']
    {f : C(X, Y)} {f' : C(X', Y')}
    (u : C(X, X')) (v : C(Y, Y')) (H : (v.comp f).Homotopy (f'.comp u))
    (x : X) (y : Y) (γ : Path (f x) y) (n : ℕ)
    (b : HomotopyGroup.Pi n (HomotopyFiber f y) (pointWithPath f x y γ)) :
    HomotopyGroup.map (basedLoopMap v rfl) rfl
      (pathTransport (loopEquivOfContractibleSourcePathInverseBasepointPath f x y γ) n
        (HomotopyGroup.map (loopEquivOfContractibleSourcePath f x y γ).invFun rfl b)) =
    pathTransport (loopEquivOfContractibleSourcePathInverseBasepointPath f' (u x) (v y)
      ((H.evalAt x).symm.trans (γ.map v.continuous))) n
      (HomotopyGroup.map (loopEquivOfContractibleSourcePath f' (u x) (v y)
        ((H.evalAt x).symm.trans (γ.map v.continuous))).invFun rfl
          (HomotopyGroup.map (homotopySquareMap u v H y) rfl b)) := by
  let a := pathTransport (loopEquivOfContractibleSourcePathInverseBasepointPath f x y γ) n
    (HomotopyGroup.map (loopEquivOfContractibleSourcePath f x y γ).invFun rfl b)
  have h := loopPrefix_homotopySquare_pi u v H x y γ n a
  rw [loopPrefix_corrected_pi, loopPrefix_corrected_pi,
    loopEquivOfContractibleSourcePath_forward_pi] at h
  have hi := congrArg (fun z ↦
    pathTransport (loopEquivOfContractibleSourcePathInverseBasepointPath f' (u x) (v y)
      ((H.evalAt x).symm.trans (γ.map v.continuous))) n
      (HomotopyGroup.map (loopEquivOfContractibleSourcePath f' (u x) (v y)
        ((H.evalAt x).symm.trans (γ.map v.continuous))).invFun rfl z)) h
  rw [loopEquivOfContractibleSourcePath_inverse_pi] at hi
  exact hi

end Topology.HomotopyFiber
