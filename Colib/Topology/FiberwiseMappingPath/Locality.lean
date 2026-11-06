/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.FiberwiseMappingPath.Restriction
public import Colib.Topology.FiberwiseMappingPath.BoundaryLifting
public import Colib.Topology.CubicalSubdivision.LocalLifting
public import Colib.Topology.CubicalSubdivision.BoundaryWeakEquivalence

/-! # Original-map weakness from local vertical endpoint lifting

The exact base-restriction homeomorphism transports every prescribed boundary
path. A finite grid then glues the actual local endpoint lifts. Literal path
scaling identifies the original map without choosing inverses to weak maps.


Implementation provenance:
`Quillen/Topology/FiberwiseMappingPath/Locality.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open scoped Topology unitInterval
universe u v w z
namespace Topology.FiberwiseMappingPath
variable {E : Type u} {F : Type v} {B : Type w}
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]

/-- Strict boundary lifting transfers through the original restriction homeomorphism. -/
theorem restrictedEndpoint_boundaryLifting (q : C(F, B)) (f : C(E, F)) (U : Set B)
    (h : CubicalSubdivision.BoundaryLifting
      (endpoint (restrictedProjection q U) (restrictedMap q f U))) :
    CubicalSubdivision.BoundaryLifting (restrictedEndpoint q f U) := by
  intro n a b hab
  let e := restrictionHomeomorph q f U
  obtain ⟨c,hc,hb⟩ := h n (e.toHomotopyEquiv.toFun.comp a) b hab
  refine ⟨e.symm.toHomotopyEquiv.toFun.comp c,?_,?_⟩
  · intro t
    change e.symm (c t.val) = a t
    rw [hc t]
    exact e.symm_apply_apply (a t)
  · ext t
    exact congrArg Subtype.val (ContinuousMap.congr_fun hb t)

/-- Exact vertical endpoint lifting is local over an open cover of the actual base. -/
theorem endpoint_boundaryLifting_of_open_cover (q : C(F, B)) (f : C(E, F))
    {J : Type z} (U : J → Set B) (hU : ∀ j, IsOpen (U j))
    (hcover : ∀ b : B,∃ j,b ∈ U j)
    (h : ∀ j,CubicalSubdivision.BoundaryLifting
      (endpoint (restrictedProjection q (U j)) (restrictedMap q f (U j)))) :
    CubicalSubdivision.BoundaryLifting (endpoint q f) := by
  apply CubicalSubdivision.BoundaryLifting.of_open_cover (endpoint q f)
    (fun j ↦ q ⁻¹' U j) (fun j ↦ (hU j).preimage q.continuous)
    (fun y ↦ hcover (q y))
  intro j
  exact restrictedEndpoint_boundaryLifting q f (U j) (h j)

/-- The conclusion is the complete empty-aware weak property of the original map. -/
theorem isWeakHomotopyEquivalence_of_open_cover (q : C(F, B)) (f : C(E, F))
    {J : Type z} (U : J → Set B) (hU : ∀ j, IsOpen (U j))
    (hcover : ∀ b : B,∃ j,b ∈ U j)
    (h : ∀ j,CubicalSubdivision.BoundaryLifting
      (endpoint (restrictedProjection q (U j)) (restrictedMap q f (U j)))) :
    IsWeakHomotopyEquivalence f := by
  have he := (endpoint_boundaryLifting_of_open_cover q f U hU hcover h).isWeakHomotopyEquivalence
  exact he.comp (isWeakHomotopyEquivalence_of_homotopyEquiv (inclusionHomotopyEquiv q f))

end Topology.FiberwiseMappingPath
