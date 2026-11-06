/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.FiberwiseMappingPath.Basic

/-! # Original vertical paths commute with arbitrary base change

The new base coordinate is retained literally, and every original path
value is preserved. No lifting or nonemptiness assumption is needed.


Implementation provenance:
`Quillen/Topology/FiberwiseMappingPath/BaseChange.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open scoped Topology unitInterval
universe u v w z
namespace Topology.FiberwiseMappingPath
variable {E : Type u} {F : Type v} {B : Type w} {T : Type z}
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B] [TopologicalSpace T]
  (q : C(F, B)) (f : C(E, F)) (g : C(T, B))

/-- The strict pullback of the target projection `q : F → B` along `g : T → B`. -/
abbrev BaseChangedTarget := {y : T × F // q y.2 = g y.1}
/-- The strict pullback of the composite `q ∘ f : E → B` along `g : T → B`. -/
abbrev BaseChangedSource := {x : T × E // q (f x.2) = g x.1}

/-- Project the base-changed target to its retained coordinate in `T`. -/
def baseChangedProjection : C(BaseChangedTarget q g,T) where
  toFun y := y.val.1
  continuous_toFun := by fun_prop

/-- Apply `f` to the original source coordinate while retaining the coordinate in `T` and the
matching equality with the base. -/
def baseChangedMap : C(BaseChangedSource q f g,BaseChangedTarget q g) where
  toFun x := ⟨(x.val.1,f x.val.2),x.property⟩
  continuous_toFun := by fun_prop

/-- The strict base change of the original fiberwise mapping-path space, matching its endpoint
base value with `g` while retaining the full path. -/
abbrev BaseChangedSpace := {x : T × Space q f // q (endpoint q f x.2) = g x.1}

/-- Base change retains the entire original path and its new fixed base coordinate. -/
def baseChangeHomeomorph :
    Space (baseChangedProjection q g) (baseChangedMap q f g) ≃ₜ BaseChangedSpace q f g where
  toFun x :=
    ⟨(x.val.1.val.1,
      ⟨(x.val.1.val.2,⟨fun t ↦ (x.val.2 t).val.2,by fun_prop⟩),
        congrArg (fun y : BaseChangedTarget q g ↦ y.val.2) x.property.1,
        fun t ↦ (x.val.2 t).property.trans
          ((congrArg g (x.property.2 t)).trans x.val.1.property.symm)⟩),
      (x.val.2 1).property.trans (congrArg g (x.property.2 1))⟩
  invFun x :=
    ⟨(⟨(x.val.1,x.val.2.val.1),(x.val.2.property.2 1).symm.trans x.property⟩,
      ⟨fun t ↦ ⟨(x.val.1,x.val.2.val.2 t),
        (x.val.2.property.2 t).trans ((x.val.2.property.2 1).symm.trans x.property)⟩,
        by fun_prop⟩),
      Subtype.ext (Prod.ext rfl x.val.2.property.1),fun _ ↦ rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply ContinuousMap.ext
      intro t
      apply Subtype.ext
      exact Prod.ext (x.property.2 t).symm rfl
  right_inv x := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · apply Continuous.subtype_mk
      apply Continuous.prodMk
      · fun_prop
      · apply ContinuousMap.continuous_of_continuous_uncurry
        change Continuous (fun x : Space (baseChangedProjection q g) (baseChangedMap q f g) ×
          unitInterval ↦
          (x.1.val.2 x.2).val.2)
        fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · apply ContinuousMap.continuous_of_continuous_uncurry
      apply Continuous.subtype_mk
      change Continuous (fun x : BaseChangedSpace q f g × unitInterval ↦
        (x.1.val.1,x.1.val.2.val.2 x.2))
      fun_prop

theorem baseChangeHomeomorph_base
    (x : Space (baseChangedProjection q g) (baseChangedMap q f g)) :
    (baseChangeHomeomorph q f g x).val.1 = x.val.1.val.1 := rfl

theorem baseChangeHomeomorph_path
    (x : Space (baseChangedProjection q g) (baseChangedMap q f g)) (t : unitInterval) :
    (baseChangeHomeomorph q f g x).val.2.val.2 t = (x.val.2 t).val.2 := rfl

theorem baseChangeHomeomorph_symm_path (x : BaseChangedSpace q f g) (t : unitInterval) :
    (((baseChangeHomeomorph q f g).symm x).val.2 t).val = (x.val.1,x.val.2.val.2 t) := rfl

theorem baseChangeHomeomorph_symm_endpoint (x : BaseChangedSpace q f g) :
    (endpoint (baseChangedProjection q g) (baseChangedMap q f g)
      ((baseChangeHomeomorph q f g).symm x)).val = (x.val.1,endpoint q f x.val.2) := rfl

end Topology.FiberwiseMappingPath
