/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalence
public import Colib.Topology.HomotopyFiber.DiscreteBase

/-!
# Weak comparisons restrict to fibers over a discrete base

A homotopy in the total space cannot change its discrete base coordinate.
This lets bijectivity on actual homotopy sets restrict to a chosen strict
fiber. The proof includes degree zero: a lifted component is placed in the
correct fiber using its comparison homotopy, not a connected-cube argument.
-/
/-! Implementation source: `Quillen/Topology/HomotopyFiber/DiscreteWeakComparison.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`; the actual maps and hypotheses are retained. -/
@[expose] public section

noncomputable section
open scoped Topology unitInterval
universe u v w z
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Topology
variable {X : Type u} {Y : Type v} {B : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace B] [DiscreteTopology B]
  (p : C(X, B)) (q : C(Y, B)) (f : C(X, Y)) (sq : q.comp f = p) (b : B)

/-- Restrict a commuting map to its actual strict fiber. -/
def discreteStrictFiberMap : C({x : X // p x = b}, {y : Y // q y = b}) where
  toFun x := ⟨f x.1, (ContinuousMap.congr_fun sq x.1).trans x.2⟩
  continuous_toFun := by fun_prop

/-- A continuous interval family has constant discrete projection. -/
theorem discrete_projection_time_constant {A : Type z} [TopologicalSpace A]
    (H : C(unitInterval × A, X)) (s t : unitInterval) (a : A) :
    p (H (s, a)) = p (H (t, a)) :=
  TotallyDisconnectedSpace.eq_of_continuous
    (fun r : unitInterval ↦ p (H (r, a))) (by fun_prop) s t

/-- Bijectivity on a homotopy set of the total spaces restricts to the same
homotopy set of each strict fiber over a discrete base. No group operation
or nonempty cube index is used, so the statement includes π₀. -/
theorem homotopyGroupMap_bijective_discreteStrictFiber {N : Type z}
    (x : {x : X // p x = b})
    (h : Function.Bijective (HomotopyGroup.map (N := N) f (x := x.1) rfl)) :
    Function.Bijective (HomotopyGroup.map (N := N)
      (discreteStrictFiberMap p q f sq b) (x := x) rfl) := by
  let iX : C({x : X // p x = b}, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let iY : C({y : Y // q y = b}, Y) := ⟨Subtype.val, continuous_subtype_val⟩
  constructor
  · intro a₀ a₁ heq
    induction a₀ using Quotient.inductionOn with | h a₀ =>
      induction a₁ using Quotient.inductionOn with | h a₁ =>
        have heq' := congrArg (HomotopyGroup.map iY
          (x := discreteStrictFiberMap p q f sq b x) rfl) heq
        have heq'' : HomotopyGroup.map f (x := x.1) rfl
            (Quotient.mk' (GenLoop.postcomp iX rfl a₀)) =
            HomotopyGroup.map f (x := x.1) rfl
              (Quotient.mk' (GenLoop.postcomp iX rfl a₁)) := heq'
        have ha := h.1 heq''
        obtain ⟨H⟩ := Quotient.exact ha
        have hover (t : unitInterval) (a : N → unitInterval) : p (H (t, a)) = b :=
          (discrete_projection_time_constant p H.toContinuousMap t 0 a).trans
            ((congrArg p (H.map_zero_left a)).trans (a₀ a).2)
        exact Quotient.sound ⟨{
          toFun := fun z ↦ ⟨H z, hover z.1 z.2⟩
          continuous_toFun := H.continuous.subtype_mk _
          map_zero_left := fun a ↦ Subtype.ext (H.map_zero_left a)
          map_one_left := fun a ↦ Subtype.ext (H.map_one_left a)
          prop' := fun t a ha ↦ Subtype.ext (H.prop t a ha) }⟩
  · intro a
    induction a using Quotient.inductionOn with | h a =>
      obtain ⟨c, hc⟩ := h.2 (Quotient.mk' (GenLoop.postcomp iY rfl a))
      induction c using Quotient.inductionOn with | h c =>
        obtain ⟨H⟩ := Quotient.exact hc
        have hover (t : unitInterval) (a' : N → unitInterval) : q (H (t, a')) = b :=
          (discrete_projection_time_constant q H.toContinuousMap t 1 a').trans
            ((congrArg q (H.map_one_left a')).trans (a a').2)
        have hc' (a' : N → unitInterval) : p (c a') = b :=
          (ContinuousMap.congr_fun sq (c a')).symm.trans
            ((congrArg q (H.map_zero_left a')).symm.trans (hover 0 a'))
        let c' : GenLoop N {x : X // p x = b} x := ⟨
          ⟨fun a' ↦ ⟨c a', hc' a'⟩, c.val.continuous.subtype_mk _⟩,
          fun a' ha' ↦ Subtype.ext (GenLoop.boundary c a' ha')⟩
        refine ⟨Quotient.mk' c', Quotient.sound ⟨?_⟩⟩
        exact {
          toFun := fun z ↦ ⟨H z, hover z.1 z.2⟩
          continuous_toFun := H.continuous.subtype_mk _
          map_zero_left := fun a' ↦ Subtype.ext (H.map_zero_left a')
          map_one_left := fun a' ↦ Subtype.ext (H.map_one_left a')
          prop' := fun t a' ha' ↦ Subtype.ext (H.prop t a' ha') }

end Topology
