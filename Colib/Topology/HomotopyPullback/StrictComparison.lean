/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyPullback.SourceEquivalence
public import Colib.Topology.HomotopyPullback.Fibration

/-! Ordinary homotopy equivalences over a base between genuine fibrations
have explicit fiberwise homotopy inverse data. -/
/-! Implementation provenance: adapted from
`Quillen/Topology/HomotopyPullback/StrictComparison.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual maps and hypotheses. -/
@[expose] public section

noncomputable section
open scoped Topology unitInterval
open unitInterval
universe u
namespace Topology.HomotopyPullback
variable {X A B : Type u} [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]
  (f : C(X, B)) (g : C(A, B))

/-- Parameter projection of the actual strict pullback. -/
def strictBaseProjection : C({z : A × X // f z.2 = g z.1}, A) := ⟨fun z ↦ z.1.1, by fun_prop⟩

/-- Universal Hurewicz lifts give a parameter-preserving equivalence with
both actual inverse homotopies, not only an unbased equivalence. -/
def strictPullbackFiberwiseEquiv (hf : HomotopyLiftingProperty f) :
    FiberwiseHomotopyEquiv (strictBaseProjection f g) (baseProjection f g) where
  toMap := strictPullbackInclusion f g
  invMap := strictPullbackRetraction f g hf
  left := (strictPullbackLeftHomotopy f g hf).symm
  right := (strictPullbackRightHomotopy f g hf).symm
  to_over := fun _ ↦ rfl
  inv_over := fun _ ↦ rfl
  left_over := fun _ _ ↦ rfl
  right_over := fun _ _ ↦ rfl

/-- The strict pullback along identity is the source itself, by its graph. -/
def graphHomeomorph : X ≃ₜ {z : B × X // f z.2 = (ContinuousMap.id B) z.1} where
  toFun x := ⟨(f x, x), rfl⟩
  invFun z := z.1.2
  left_inv _ := rfl
  right_inv z := by apply Subtype.ext; exact Prod.ext z.2 rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- A fibration is fiberwise homotopy equivalent to its actual mapping-path
replacement, with exactly the constant-path section as forward map. -/
def fibrationReplacementFiberwiseEquiv (hf : HomotopyLiftingProperty f) :
    FiberwiseHomotopyEquiv f (baseProjection f (ContinuousMap.id B)) :=
  (FiberwiseHomotopyEquiv.ofHomeomorph (p := f)
    (q := strictBaseProjection f (ContinuousMap.id B)) (graphHomeomorph f) (fun _ ↦ rfl)).trans
    (strictPullbackFiberwiseEquiv f (ContinuousMap.id B) hf)

end Topology.HomotopyPullback

namespace Topology
variable {X Y B : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace B]

/-- A homotopy equivalence over a common base between actual Hurewicz
fibrations has a continuous inverse over that base and actual fiberwise
inverse homotopies. Only the forward ordinary equivalence is given. -/
def fiberwiseEquivOfFibrationHomotopyEquiv (p : C(X, B)) (q : C(Y, B))
    (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
    (e : ContinuousMap.HomotopyEquiv X Y) (sq : q.comp e.toFun = p) :
    FiberwiseHomotopyEquiv p q := by
  subst p
  let EX := HomotopyPullback.fibrationReplacementFiberwiseEquiv (q.comp e.toFun) hp
  let EY := HomotopyPullback.fibrationReplacementFiberwiseEquiv q hq
  let EM := HomotopyPullback.sourceFiberwiseEquiv (ContinuousMap.id B) q e
  let D := (EX.trans EM).trans EY.symm
  have hs : EM.toMap.comp EX.toMap = EY.toMap.comp e.toFun := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    rfl
  have hD : D.toMap = EY.invMap.comp (EY.toMap.comp e.toFun) := by
    change EY.invMap.comp (EM.toMap.comp EX.toMap) = _
    rw [hs]
  let H : e.toFun.Homotopy D.toMap :=
    ((EY.left.comp (ContinuousMap.Homotopy.refl e.toFun)).symm).cast rfl (by rw [hD]; rfl)
  have hH : HomotopyOver (q.comp e.toFun) q H :=
    (EY.left_over.comp (HomotopyOver.refl e.toFun (fun _ ↦ rfl))).symm
  exact D.replaceForward e.toFun H hH

@[simp] theorem fiberwiseEquivOfFibrationHomotopyEquiv_toMap
    (p : C(X, B)) (q : C(Y, B)) (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
    (e : ContinuousMap.HomotopyEquiv X Y) (sq : q.comp e.toFun = p) :
    (fiberwiseEquivOfFibrationHomotopyEquiv p q hp hq e sq).toMap = e.toFun := by
  subst p
  rfl

end Topology
