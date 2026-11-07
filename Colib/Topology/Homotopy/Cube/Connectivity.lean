/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Topology.Homotopy.HomotopyGroup
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Connectivity of the actual cubical homotopy domain

The coordinatewise contraction acts on Mathlib's original cube. Its boundary
is path connected as soon as there are two distinct coordinate directions.
The boundary paths fix one endpoint coordinate at a time.
-/
@[expose] public noncomputable section
open scoped Topology unitInterval

namespace Cube

variable (N : Type*)

/-- Coordinatewise multiplication contracts the original cube to its zero corner. -/
theorem contractibleSpace : ContractibleSpace (N → unitInterval) := by
  apply (contractible_iff_id_nullhomotopic _).mpr
  refine ⟨fun _ => 0, ⟨ContinuousMap.Homotopy.symm ?_⟩⟩
  exact {
    toFun := fun z i => z.1 * z.2 i
    continuous_toFun := by
      apply continuous_pi
      intro i
      exact ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd))).subtype_mk _
    map_zero_left := by intro x; funext i; simp
    map_one_left := by intro x; funext i; simp }

/-- A path between cube points with one common endpoint coordinate stays in the boundary. -/
theorem joinedIn_boundary_of_eq {x y : N → unitInterval} (i : N)
    (hi : x i = 0 ∨ x i = 1) (hxy : y i = x i) :
    JoinedIn (boundary N) x y := by
  classical
  let : ContractibleSpace unitInterval := by
    apply (contractible_iff_id_nullhomotopic _).mpr
    refine ⟨0, ⟨ContinuousMap.Homotopy.symm ?_⟩⟩
    exact {
      toFun := fun z => z.1 * z.2
      continuous_toFun := ((continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd)).subtype_mk _
      map_zero_left := by intro x; simp
      map_one_left := by intro x; simp }
  let p : ∀ j, Path (x j) (y j) := fun j =>
    if h : j = i then (Path.refl (x j)).cast rfl (by simpa only [h] using hxy)
    else PathConnectedSpace.somePath (x j) (y j)
  refine ⟨Path.pi p, fun t => ⟨i, ?_⟩⟩
  change p i t = 0 ∨ p i t = 1
  simpa only [p, dite_eq_left rfl, Path.cast_coe, Path.refl_apply] using hi

/-- Every boundary point is joined inside the boundary to the original zero corner. -/
theorem joinedIn_boundary_zero [Nontrivial N] {x : N → unitInterval}
    (hx : x ∈ boundary N) : JoinedIn (boundary N) x (fun _ => 0) := by
  classical
  obtain ⟨i, hi⟩ := hx
  obtain ⟨j, hji⟩ := exists_ne i
  let y : N → unitInterval := Function.update (fun _ => 0) i (x i)
  have hxy : JoinedIn (boundary N) x y :=
    joinedIn_boundary_of_eq N i hi (Function.update_self ..)
  have hyj : y j = 0 := Function.update_of_ne hji ..
  exact hxy.trans (joinedIn_boundary_of_eq N j (.inl hyj) hyj.symm)

/-- Mathlib's actual cube boundary is path connected in at least two directions. -/
theorem isPathConnected_boundary [Nontrivial N] : IsPathConnected (boundary N) := by
  obtain ⟨i⟩ := (inferInstance : Nonempty N)
  refine ⟨fun _ => 0, ⟨i, Or.inl rfl⟩, ?_⟩
  intro x hx
  exact (joinedIn_boundary_zero N hx).symm

end Cube
