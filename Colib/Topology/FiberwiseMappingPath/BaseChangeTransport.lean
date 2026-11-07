/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.FiberwiseMappingPath.BaseChange
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalenceProperty

/-! # Literal base-change transport through an over-base target homeomorphism

Implementation provenance:
`Quillen/Topology/FiberwiseMappingPath/BaseChangeTransport.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open scoped Topology
universe u
namespace Topology.FiberwiseMappingPath
variable {E F F' B D : Type u}
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace F']
  [TopologicalSpace B] [TopologicalSpace D]

/-- The original source point and the new parameter remain unchanged while
only the displayed homeomorphic target coordinates are transported. -/
theorem baseChangedMap_isWeak_of_targetHomeomorph
    (q : C(F, B)) (f : C(E, F)) (g : C(D, B))
    (q' : C(F', B)) (f' : C(E, F')) (e : F' ≃ₜ F)
    (hf : ∀ x : E,e (f' x) = f x) (hq : ∀ y : F',q (e y) = q' y)
    (hweak : IsWeakHomotopyEquivalence (baseChangedMap q' f' g)) :
    IsWeakHomotopyEquivalence (baseChangedMap q f g) := by
  let es : BaseChangedSource q f g ≃ₜ BaseChangedSource q' f' g :=
    Homeomorph.setCongr (by
      ext x
      change q (f x.2) = g x.1 ↔ q' (f' x.2) = g x.1
      rw [← hq,hf])
  let et : BaseChangedTarget q' g ≃ₜ BaseChangedTarget q g := {
    toFun x := ⟨(x.val.1,e x.val.2),(hq _).trans x.property⟩
    invFun x := ⟨(x.val.1,e.symm x.val.2),by
      have he := hq (e.symm x.val.2)
      rw [e.apply_symm_apply] at he
      exact he.symm.trans x.property⟩
    left_inv x := Subtype.ext (Prod.ext rfl (e.symm_apply_apply x.val.2))
    right_inv x := Subtype.ext (Prod.ext rfl (e.apply_symm_apply x.val.2))
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  have heq : et.toHomotopyEquiv.toFun.comp
      ((baseChangedMap q' f' g).comp es.toHomotopyEquiv.toFun) = baseChangedMap q f g := by
    apply ContinuousMap.ext
    intro x
    exact Subtype.ext (Prod.ext rfl (hf x.val.2))
  rw [← heq]
  exact (isWeakHomotopyEquivalence_of_homotopyEquiv et.toHomotopyEquiv).comp
    (hweak.comp (isWeakHomotopyEquivalence_of_homotopyEquiv es.toHomotopyEquiv))

end Topology.FiberwiseMappingPath
