/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.Connectivity.Basic
public import Colib.Topology.HomotopyFiber.ContractibleBase

/-!
# Finite connectivity from actual homotopy-set vanishing

A map into a connected target is finitely connected when the source homotopy sets vanish
below the range and the target homotopy sets vanish through it. The proof uses the actual
mapping-path fibration and its genuine strict-fiber comparison at every original fiber point.
The map to a point retains the sharper source vanishing bound. Components and nonemptiness
are explicit; no space replacement is used in either conclusion.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/HomotopyGroups/Connectivity/Vanishing.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, finite bounds,
whole path families and universe parameters are retained in their native owners. -/
@[expose] public section
noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace Topology
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The original map has the finite fiber bound when its adjacent source/target groups vanish. -/
theorem isHomotopyConnectedMap_of_vanishing (f : C(X, Y)) (x₀ : X)
    [PathConnectedSpace Y] (n : ℕ)
    (hX : ∀ x k, k < n → Subsingleton (HomotopyGroup.Pi k X x))
    (hY : ∀ y k, k ≤ n → Subsingleton (HomotopyGroup.Pi k Y y)) :
    IsHomotopyConnectedMap f n where
  fiber_nonempty y := by
    let γ := (PathConnectedSpace.joined (f x₀) y).somePath
    exact ⟨⟨(x₀, γ.toContinuousMap), γ.source, γ.target⟩⟩
  fiber_subsingleton y z k hk := by
    let e := (MappingPath.endpointFiberHomeomorph f y).symm
    let w := e z
    let eX := (MappingPath.inclusionHomotopyEquiv f).symm
    let : Subsingleton (HomotopyGroup.Pi k (MappingPath f) w.1) := by
      let := hX (eX w.1) k hk
      exact (homotopyGroupMap_bijective_of_homotopyEquiv
        eX (x := w.1) (y := eX w.1) rfl k).injective.subsingleton
    let := hY y (k + 1) (by omega)
    let : Subsingleton (HomotopyGroup.Pi k
        (HomotopyFiber (MappingPath.endpoint f) y)
        (HomotopyFiber.basepoint (MappingPath.endpoint f) y w.1 w.2)) :=
      HomotopyFiber.subsingleton_homotopyGroup_of_adjacent
        (MappingPath.endpoint f) y w.1 w.2 k
        (fun _ _ _ ↦ Subsingleton.elim _ _)
        (fun b ↦ ⟨default, Subsingleton.elim _ _⟩)
    let : Subsingleton (HomotopyGroup.Pi k {x : MappingPath f //
        MappingPath.endpoint f x = y} w) :=
      (homotopyGroupMap_bijective_of_homotopyEquiv
        (HomotopyFiber.strictFiberHomotopyEquivOfLifting (MappingPath.endpoint f)
          (MappingPath.endpoint_homotopyLiftingProperty f) y)
        (x := w) (y := HomotopyFiber.basepoint (MappingPath.endpoint f) y w.1 w.2)
        rfl k).injective.subsingleton
    exact (homotopyGroupMap_bijective_of_homotopyEquiv
      e.toHomotopyEquiv (x := z) (y := e z) rfl k).injective.subsingleton

/-- The original constant map to a point has exactly the range supplied by source vanishing. -/
theorem isHomotopyConnectedMap_const_of_vanishing (x₀ : X) (n : ℕ)
    (hX : ∀ x k, k < n → Subsingleton (HomotopyGroup.Pi k X x)) :
    IsHomotopyConnectedMap (ContinuousMap.const X (PUnit.unit : PUnit.{u + 1})) n where
  fiber_nonempty y := by
    exact ⟨⟨(x₀, ContinuousMap.const _ y), Subsingleton.elim _ _, rfl⟩⟩
  fiber_subsingleton y z k hk := by
    let H : (ContinuousMap.id PUnit.{u + 1}).Homotopy (ContinuousMap.const _ y) :=
      { toFun := fun _ ↦ y
        continuous_toFun := continuous_const
        map_zero_left := fun _ ↦ Subsingleton.elim _ _
        map_one_left := fun _ ↦ rfl }
    let e := HomotopyFiber.projectionEquivOfContraction
      (ContinuousMap.const X (PUnit.unit : PUnit.{u + 1})) y H
    let := hX (e z) k hk
    exact (homotopyGroupMap_bijective_of_homotopyEquiv
      e (x := z) (y := e z) rfl k).injective.subsingleton

end Topology
