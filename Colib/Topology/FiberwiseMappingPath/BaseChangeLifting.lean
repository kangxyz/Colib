/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.FiberwiseMappingPath.BaseChange
public import Colib.Topology.FiberwiseMappingPath.Locality

/-! # Exact vertical endpoint lifting after arbitrary base change

The finite cube lift keeps the new base coordinate supplied by the target
map. The original boundary source and every original boundary path value
are retained by the actual base-change homeomorphism.


Implementation provenance:
`Quillen/Topology/FiberwiseMappingPath/BaseChangeLifting.lean`
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

/-- Original vertical endpoint RLP is stable under every actual base map. -/
theorem endpoint_boundaryLifting_baseChange
    (q : C(F, B)) (f : C(E, F)) (g : C(T, B))
    (h : CubicalSubdivision.BoundaryLifting (endpoint q f)) :
    CubicalSubdivision.BoundaryLifting
      (endpoint (baseChangedProjection q g) (baseChangedMap q f g)) := by
  intro n a b hab
  let e := baseChangeHomeomorph q f g
  let a₀ : C(CubicalSubdivision.Boundary n,Space q f) :=
    ⟨fun t ↦ (e (a t)).val.2,by fun_prop⟩
  let b₀ : C(CubicalSubdivision.Cube n,F) := ⟨fun t ↦ (b t).val.2,by fun_prop⟩
  have hab₀ (t : CubicalSubdivision.Boundary n) : endpoint q f (a₀ t) = b₀ t.val :=
    congrArg (fun y : BaseChangedTarget q g ↦ y.val.2) (hab t)
  obtain ⟨c,hc,hb⟩ := h n a₀ b₀ hab₀
  let l : C(CubicalSubdivision.Cube n,BaseChangedSpace q f g) := {
    toFun t := ⟨((b t).val.1,c t),
      (congrArg q (ContinuousMap.congr_fun hb t)).trans (b t).property⟩
    continuous_toFun := by fun_prop }
  refine ⟨e.symm.toHomotopyEquiv.toFun.comp l,?_,?_⟩
  · intro t
    apply e.injective
    change e (e.symm (l t.val)) = e (a t)
    rw [e.apply_symm_apply]
    apply Subtype.ext
    apply Prod.ext
    · have hh := congrArg (fun y : BaseChangedTarget q g ↦ y.val.1) (hab t)
      exact hh.symm.trans ((a t).property.2 1)
    · exact hc t
  · apply ContinuousMap.ext
    intro t
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact ContinuousMap.congr_fun hb t

/-- The resulting original base-changed map is weak in every finite dimension. -/
theorem baseChangedMap_isWeakHomotopyEquivalence
    (q : C(F, B)) (f : C(E, F)) (g : C(T, B))
    (h : CubicalSubdivision.BoundaryLifting (endpoint q f)) :
    IsWeakHomotopyEquivalence (baseChangedMap q f g) := by
  have he := (endpoint_boundaryLifting_baseChange q f g h).isWeakHomotopyEquivalence
  exact he.comp (isWeakHomotopyEquivalence_of_homotopyEquiv
    (inclusionHomotopyEquiv (baseChangedProjection q g) (baseChangedMap q f g)))

/-- Every smaller base chart retains exact endpoint lifting, including empty subsets. -/
theorem endpoint_boundaryLifting_restriction
    (q : C(F, B)) (f : C(E, F)) (U : Set B)
    (h : CubicalSubdivision.BoundaryLifting (endpoint q f)) :
    CubicalSubdivision.BoundaryLifting
      (endpoint (restrictedProjection q U) (restrictedMap q f U)) := by
  intro n a b hab
  let e := restrictionHomeomorph q f U
  let a₀ : C(CubicalSubdivision.Boundary n,Space q f) :=
    ⟨fun t ↦ (e.symm (a t)).val,by fun_prop⟩
  let b₀ : C(CubicalSubdivision.Cube n,F) := ⟨fun t ↦ (b t).val,by fun_prop⟩
  have hab₀ (t : CubicalSubdivision.Boundary n) : endpoint q f (a₀ t) = b₀ t.val :=
    congrArg Subtype.val (hab t)
  obtain ⟨c,hc,hb⟩ := h n a₀ b₀ hab₀
  let l : C(CubicalSubdivision.Cube n,RestrictedSpace q f U) := {
    toFun t := ⟨c t,(congrArg q (ContinuousMap.congr_fun hb t)) ▸ (b t).property⟩
    continuous_toFun := by fun_prop }
  refine ⟨e.toHomotopyEquiv.toFun.comp l,?_,?_⟩
  · intro t
    apply e.symm.injective
    change e.symm (e (l t.val)) = e.symm (a t)
    rw [e.symm_apply_apply]
    exact Subtype.ext (hc t)
  · ext t
    exact ContinuousMap.congr_fun hb t

end Topology.FiberwiseMappingPath
