/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Topology.Homotopy.HomotopyGroup.PathComponent
public import Colib.Topology.Homotopy.HomotopyGroup.PathComponentPositive
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalenceConnected

/-!
Implementation provenance:
`Quillen/Topology/HomotopyGroups/PathComponentWeakEquivalence.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Restriction of an original weak equivalence to specified path components -/
@[expose] public section
noncomputable section
universe u v
namespace Topology
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The literal restriction, with its target component selected by a genuine joining path. -/
def pathComponentMap (f : C(X, Y)) (x : X) (y : Y) (h : Joined (f x) y) :
    C(pathComponent x, pathComponent y) :=
  ⟨fun z ↦ ⟨f z.val, h.symm.trans (z.property.map f.continuous)⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

@[simp] theorem pathComponentMap_val (f : C(X, Y)) (x : X) (y : Y)
    (h : Joined (f x) y) (z : pathComponent x) :
    (pathComponentMap f x y h z).val = f z.val := rfl

/-- The component square is strictly the square of the original continuous maps. -/
theorem pathComponentMap_square (f : C(X, Y)) (x : X) (y : Y)
    (h : Joined (f x) y) :
    (pathComponentInclusion y).comp (pathComponentMap f x y h) =
      f.comp (pathComponentInclusion x) := rfl

/-- Restriction preserves weak equivalence with the original underlying map. -/
theorem IsWeakHomotopyEquivalence.pathComponentMap {f : C(X, Y)}
    (hf : IsWeakHomotopyEquivalence f) (x : X) (y : Y) (h : Joined (f x) y) :
    IsWeakHomotopyEquivalence (Topology.pathComponentMap f x y h) := by
  let : PathConnectedSpace (pathComponent x) :=
    isPathConnected_iff_pathConnectedSpace.mp isPathConnected_pathComponent
  let : PathConnectedSpace (pathComponent y) :=
    isPathConnected_iff_pathConnectedSpace.mp isPathConnected_pathComponent
  let x₀ : pathComponent x := ⟨x, mem_pathComponent_self x⟩
  apply isWeakHomotopyEquivalence_of_connected _ x₀
  intro n
  have hi := homotopyGroupMap_pathComponent_bijective (N := Fin (n + 1)) x
  have hj := homotopyGroupMap_bijective_at_all_points (pathComponentInclusion y)
    ⟨y, mem_pathComponent_self y⟩ (n + 1)
    (homotopyGroupMap_pathComponent_bijective y) (Topology.pathComponentMap f x y h x₀)
  have hc := homotopyGroupMap_bijective_comp (pathComponentInclusion x) f
    (x := x₀) rfl rfl (n + 1) hi (hf.homotopy_bijective x (n + 1))
  have he : HomotopyGroup.map (N := Fin (n + 1))
      (f.comp (pathComponentInclusion x)) (x := x₀) rfl =
      HomotopyGroup.map (N := Fin (n + 1)) (pathComponentInclusion y) rfl ∘
        HomotopyGroup.map (N := Fin (n + 1)) (Topology.pathComponentMap f x y h) rfl := by
    funext a
    exact HomotopyGroup.map_comp (Topology.pathComponentMap f x y h) rfl
      (pathComponentInclusion y) rfl a
  rw [he] at hc
  exact (hj.of_comp_iff' _).mp hc

/-- The specified ambient basepoint track restricts without changing any point. -/
def pathComponentMapBasepointPath (f : C(X, Y)) (x : X) (y : Y)
    (p : Path (f x) y) :
    Path (pathComponentMap f x y ⟨p⟩ ⟨x, mem_pathComponent_self x⟩)
      ⟨y, mem_pathComponent_self y⟩ := pathComponentPath p

@[simp] theorem pathComponentMapBasepointPath_val (f : C(X, Y)) (x : X) (y : Y)
    (p : Path (f x) y) (t : unitInterval) :
    (pathComponentMapBasepointPath f x y p t).val = p t := rfl

end Topology
