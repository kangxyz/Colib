/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.FiberwiseMappingPath.BaseChange
public import Colib.Topology.Homotopy.HomotopyGroup.WeakLocality

/-! # Exact weak chart transport after a displayed base change

A supplied homeomorphic chart of the original map transports to its literal
pullback. The new parameter and original point coordinates are preserved.
Weakness is assumed only for that actual base-changed chart map, never inferred
from ordinary weakness before base change.


Implementation provenance:
`Quillen/Topology/FiberwiseMappingPath/BaseChangeCharts.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open Topology.CubicalSubdivision


noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u
namespace Topology.FiberwiseMappingPath
open CubicalSubdivision
variable {E F B D A C : Type u}
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
  [TopologicalSpace D] [TopologicalSpace A] [TopologicalSpace C]

/-- The exact restriction over a pulled-back target chart is weak when its
actual chart model after the same base change is weak. -/
theorem baseChangedRestriction_isWeak_of_chart
    (q : C(F, B)) (f : C(E, F)) (g : C(D, B)) (W : Set F)
    (k : C(A, C)) (r : C(C, B))
    (es : {x : E // f x ∈ W} ≃ₜ A) (et : C ≃ₜ W)
    (hsq : ∀ x : {x : E // f x ∈ W},(et (k (es x))).val = f x.val)
    (hbase : ∀ y : C,q (et y).val = r y)
    (hweak : IsWeakHomotopyEquivalence (baseChangedMap r k g)) :
    IsWeakHomotopyEquivalence (restriction (baseChangedMap q f g)
      {z : BaseChangedTarget q g | z.val.2 ∈ W}) := by
  let s : {x : BaseChangedSource q f g // f x.val.2 ∈ W} ≃ₜ
      BaseChangedSource r k g := {
    toFun x := ⟨(x.val.val.1,es ⟨x.val.val.2,x.property⟩),
      (hbase _).symm.trans ((congrArg q (hsq ⟨x.val.val.2,x.property⟩)).trans x.val.property)⟩
    invFun x := ⟨⟨(x.val.1,(es.symm x.val.2).val),by
      have he := hsq (es.symm x.val.2)
      rw [es.apply_symm_apply] at he
      exact (congrArg q he).symm.trans ((hbase _).trans x.property)⟩,
      (es.symm x.val.2).property⟩
    left_inv x := by
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext rfl (congrArg Subtype.val (es.symm_apply_apply ⟨x.val.val.2,x.property⟩))
    right_inv x := by
      apply Subtype.ext
      exact Prod.ext rfl (es.apply_symm_apply x.val.2)
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let t : BaseChangedTarget r g ≃ₜ
      {z : BaseChangedTarget q g // z.val.2 ∈ W} := {
    toFun x := ⟨⟨(x.val.1,(et x.val.2).val),(hbase _).trans x.property⟩,(et x.val.2).property⟩
    invFun x := ⟨(x.val.val.1,et.symm ⟨x.val.val.2,x.property⟩),by
      have he := hbase (et.symm ⟨x.val.val.2,x.property⟩)
      rw [et.apply_symm_apply] at he
      exact he.symm.trans x.val.property⟩
    left_inv x := by
      apply Subtype.ext
      exact Prod.ext rfl (et.symm_apply_apply x.val.2)
    right_inv x := by
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext rfl (congrArg Subtype.val (et.apply_symm_apply ⟨x.val.val.2,x.property⟩))
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  have heq : t.toHomotopyEquiv.toFun.comp ((baseChangedMap r k g).comp s.toHomotopyEquiv.toFun) =
      restriction (baseChangedMap q f g) {z : BaseChangedTarget q g | z.val.2 ∈ W} := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl (hsq ⟨x.val.val.2,x.property⟩)
  rw [← heq]
  exact (isWeakHomotopyEquivalence_of_homotopyEquiv t.toHomotopyEquiv).comp
    (hweak.comp (isWeakHomotopyEquivalence_of_homotopyEquiv s.toHomotopyEquiv))

end Topology.FiberwiseMappingPath
