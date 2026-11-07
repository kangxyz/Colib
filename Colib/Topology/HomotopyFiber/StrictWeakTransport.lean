/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.WeakSourceEquivalence
public import Colib.Topology.HomotopyPullback.RetractionBaseChange

/-! # Strict fibers and strict pullbacks of genuine fibrations

Implementation provenance:
`Quillen/Topology/HomotopyFiber/StrictWeakTransport.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u
namespace Topology
namespace HomotopyPullback
variable {E A B : Type u} [TopologicalSpace E] [TopologicalSpace A] [TopologicalSpace B]

/-- The actual fiber of a strict pullback is the original strict fiber. -/
def strictPullbackFiberHomeomorph (f : C(E, B)) (g : C(A, B)) (a : A) :
    {z : {z : A × E // f z.2 = g z.1} // strictBaseProjection f g z = a} ≃ₜ
      {e : E // f e = g a} where
  toFun z := ⟨z.1.1.2, z.1.2.trans (congrArg g z.2)⟩
  invFun z := ⟨⟨(a, z.1), z.2⟩, rfl⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext z.2.symm rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end HomotopyPullback
namespace HomotopyFiber
variable {X Y B : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace B]
  (f : C(X, B)) (g : C(Y, B)) (u : C(X, Y)) (sq : g.comp u = f) (b : B)

/-- The original map between the actual strict fibers over a common base. -/
def strictMapOver : C({x : X // f x = b}, {y : Y // g y = b}) where
  toFun z := ⟨u z.1, (ContinuousMap.congr_fun sq z.1).trans z.2⟩
  continuous_toFun := by fun_prop

/-- A weak total map over a fixed base induces a weak original strict-fiber
map when both displayed projections are genuine fibrations. -/
theorem strictMapOver_isWeakHomotopyEquivalence
    (hf : HomotopyLiftingProperty f) (hg : HomotopyLiftingProperty g)
    (hu : IsWeakHomotopyEquivalence u) :
    IsWeakHomotopyEquivalence (strictMapOver f g u sq b) := by
  have hs := (mapOver_isWeakHomotopyEquivalence f g u sq b hu).comp
    (isWeakHomotopyEquivalence_of_homotopyEquiv (strictFiberHomotopyEquivOfLifting f hf b))
  exact IsWeakHomotopyEquivalence.of_comp_right
    (f := strictMapOver f g u sq b) (g := strictFiberInclusion g b) hs
    (isWeakHomotopyEquivalence_of_homotopyEquiv (strictFiberHomotopyEquivOfLifting g hg b))

end HomotopyFiber
end Topology
