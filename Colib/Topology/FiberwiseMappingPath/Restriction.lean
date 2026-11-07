/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.FiberwiseMappingPath.Basic

/-! # Exact restriction of vertical mapping paths

Restriction is by a subset of the displayed base. Every stored path stays
in that subset automatically. The homeomorphism retains every original
path value; it requires no openness or separation assumption.


Implementation provenance:
`Quillen/Topology/FiberwiseMappingPath/Restriction.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open scoped Topology unitInterval
universe u v w
namespace Topology.FiberwiseMappingPath
variable {E : Type u} {F : Type v} {B : Type w}
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]
  (q : C(F, B)) (f : C(E, F)) (U : Set B)

/-- The source points whose image under `q ∘ f` lies in the base subset `U`. -/
abbrev RestrictedSource := {x : E // q (f x) ∈ U}
/-- The target points whose image under `q` lies in the base subset `U`. -/
abbrev RestrictedTarget := {y : F // q y ∈ U}

/-- The restriction of the target projection `q` to a continuous map with codomain `U`. -/
def restrictedProjection : C(RestrictedTarget q U,U) where
  toFun y := ⟨q y.val,y.property⟩
  continuous_toFun := by fun_prop

/-- The restriction of `f` between the source and target subspaces over `U`. -/
def restrictedMap : C(RestrictedSource q f U,RestrictedTarget q U) where
  toFun x := ⟨f x.val,x.property⟩
  continuous_toFun := by fun_prop

/-- The vertical mapping-path points whose endpoint projects into the base subset `U`. -/
abbrev RestrictedSpace := {z : Space q f // q (endpoint q f z) ∈ U}

/-- The original endpoint restricted over the displayed base subset. -/
def restrictedEndpoint : C(RestrictedSpace q f U,RestrictedTarget q U) where
  toFun z := ⟨endpoint q f z.val,z.property⟩
  continuous_toFun := by fun_prop

/-- Pack each original path point in the restricted target, or forget that
membership proof. Both operations retain all original coordinates. -/
def restrictionHomeomorph : RestrictedSpace q f U ≃ₜ
    Space (restrictedProjection q U) (restrictedMap q f U) where
  toFun z :=
    ⟨(⟨z.val.val.1,(z.val.property.2 1) ▸ z.property⟩,
      ⟨fun t ↦ ⟨z.val.val.2 t,
        ((z.val.property.2 t).trans (z.val.property.2 1).symm) ▸ z.property⟩,
        by fun_prop⟩),
      Subtype.ext z.val.property.1,fun t ↦ Subtype.ext (z.val.property.2 t)⟩
  invFun z :=
    ⟨⟨(z.val.1.val,⟨fun t ↦ (z.val.2 t).val,by fun_prop⟩),
      congrArg Subtype.val z.property.1,fun t ↦ congrArg Subtype.val (z.property.2 t)⟩,
      (z.val.2 1).property⟩
  left_inv z := rfl
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · ext t
      rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · apply ContinuousMap.continuous_of_continuous_uncurry
      apply Continuous.subtype_mk
      change Continuous (fun z : RestrictedSpace q f U × unitInterval ↦ z.1.val.val.2 z.2)
      fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun z : Space (restrictedProjection q U) (restrictedMap q f U) ×
        unitInterval ↦
        (z.1.val.2 z.2).val)
      fun_prop

theorem restrictionHomeomorph_source (z : RestrictedSpace q f U) :
    (source (restrictedProjection q U) (restrictedMap q f U)
      (restrictionHomeomorph q f U z)).val = source q f z.val := rfl

theorem restrictionHomeomorph_path (z : RestrictedSpace q f U) (t : unitInterval) :
    ((restrictionHomeomorph q f U z).val.2 t).val = z.val.val.2 t := rfl

theorem restrictionHomeomorph_symm_path
    (z : Space (restrictedProjection q U) (restrictedMap q f U)) (t : unitInterval) :
    ((restrictionHomeomorph q f U).symm z).val.val.2 t = (z.val.2 t).val := rfl

/-- Exact endpoint commutation as continuous maps, not just a path-class comparison. -/
theorem restrictionHomeomorph_endpoint :
    (endpoint (restrictedProjection q U) (restrictedMap q f U)).comp
      (restrictionHomeomorph q f U).toHomotopyEquiv.toFun = restrictedEndpoint q f U := rfl

end Topology.FiberwiseMappingPath
