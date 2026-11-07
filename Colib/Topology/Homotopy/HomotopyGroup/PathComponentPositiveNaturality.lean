/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.PathComponentWeakEquivalence
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransportNaturality
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransportGroup

/-!
Implementation provenance:
`Quillen/Topology/HomotopyGroups/PathComponentPositiveNaturality.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Naturality of the original component homotopy-group equivalence

The literal restriction of a continuous map to specified path components uses
the supplied basepoint path. Its positive homotopy-group map commutes with the
original component inclusions after transport along exactly that path and its
literal restriction. The proof uses the strict inclusion square and the exact
pointwise track; no replacement path or basepoint choice is introduced.
-/

@[expose] public section

noncomputable section

universe u v

namespace Topology

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The original inclusion square and original restricted track give a commuting
square of path-corrected maps in every finite homotopy degree. -/
theorem pathComponentMap_homotopyGroupMap_naturality
    (f : C(X, Y)) (x : X) (y : Y) (p : Path (f x) y) (n : ℕ)
    (a : HomotopyGroup.Pi n (pathComponent x) ⟨x, mem_pathComponent_self x⟩) :
    HomotopyGroup.map (pathComponentInclusion y) rfl
      (pathTransport (pathComponentMapBasepointPath f x y p) n
        (HomotopyGroup.map (pathComponentMap f x y ⟨p⟩) rfl a)) =
      pathTransport p n (HomotopyGroup.map f rfl
        (HomotopyGroup.map (pathComponentInclusion x) rfl a)) := by
  calc
    _ = pathTransport p n
        (HomotopyGroup.map (pathComponentInclusion y) rfl
          (HomotopyGroup.map (pathComponentMap f x y ⟨p⟩) rfl a)) :=
      (pathTransport_naturality_of_track (pathComponentInclusion y)
        (pathComponentMapBasepointPath f x y p) p rfl rfl (fun _ ↦ rfl) n _).symm
    _ = _ := congrArg (pathTransport p n)
      ((HomotopyGroup.map_comp (pathComponentMap f x y ⟨p⟩) rfl
        (pathComponentInclusion y) rfl a).symm.trans
          (HomotopyGroup.map_comp (pathComponentInclusion x) rfl f rfl a))

/-- Naturality of the positive component equivalence retains both original
component inclusions and the exact supplied basepoint path. -/
theorem pathComponentPiMulEquiv_naturality_apply
    (f : C(X, Y)) (x : X) (y : Y) (p : Path (f x) y) (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (pathComponent x) ⟨x, mem_pathComponent_self x⟩) :
    pathComponentPiMulEquiv y n
      (pathTransportMulEquiv (pathComponentMapBasepointPath f x y p) n
        (HomotopyGroup.piMap n (pathComponentMap f x y ⟨p⟩) rfl a)) =
      pathTransportMulEquiv p n (HomotopyGroup.piMap n f rfl (pathComponentPiMulEquiv x n a)) :=
  pathComponentMap_homotopyGroupMap_naturality f x y p (n + 1) a

/-- The commuting square as an equality of the actual path-corrected group maps. -/
theorem pathComponentPiMulEquiv_naturality
    (f : C(X, Y)) (x : X) (y : Y) (p : Path (f x) y) (n : ℕ) :
    (pathComponentPiMulEquiv y n).toMonoidHom.comp
      ((pathTransportMulEquiv (pathComponentMapBasepointPath f x y p) n).toMonoidHom.comp
        (HomotopyGroup.piMap n (pathComponentMap f x y ⟨p⟩)
          (x := ⟨x, mem_pathComponent_self x⟩) rfl)) =
      ((pathTransportMulEquiv p n).toMonoidHom.comp (HomotopyGroup.piMap n f (x := x) rfl)).comp
        (pathComponentPiMulEquiv x n).toMonoidHom := by
  apply MonoidHom.ext
  exact pathComponentPiMulEquiv_naturality_apply f x y p n

end Topology
