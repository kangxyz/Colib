/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.CappedTetrahedronCocycle
public import Colib.Topology.HomotopyFiber.SphericalCappedTriangle

/-!
# A marked cap value on the actual based singular triangles

Simple connectedness supplies a null path for every original based loop.
The constant loop is assigned its literal constant cap. Each triangle then
uses these same chosen caps for its actual three edges. The ambient cocycle
and spherical marking apply to these exact choices.
-/

/-! Implementation source: `Quillen/Topology/HomotopyFiber/NormalizedCapValue.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual fiber paths, source returns,
ordered face maps and signs are retained directly on native singular simplices. -/
@[expose] public section

open Convexity
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open StdSimplex FundamentalGroupoid
open scoped Topology
universe u

namespace Topology.HomotopyFiber
variable {Y : Type u} [TopologicalSpace Y] [SimplyConnectedSpace Y] (y : Y)

/-- An actual loop null path, choosing the constant cap on the literal constant loop. -/
def normalizedLoopCap (p : Path y y) : Path p (Path.refl y) := by
  classical
  exact if hp : p = Path.refl y then (Path.refl (Path.refl y)).cast hp rfl else
    LoopComponentTransport.pathOfPathHomotopy
      (Classical.choice (SimplyConnectedSpace.paths_homotopic p (Path.refl y)))

/-- The selected cap at the constant loop is exactly constant for its entire time. -/
@[simp] theorem normalizedLoopCap_refl :
    normalizedLoopCap y (Path.refl y) = Path.refl (Path.refl y) := by
  simp only [normalizedLoopCap, dite_eq_left, Path.cast_rfl_rfl]

/-- The cap value of an actual triangle with every vertex at the displayed basepoint. -/
def basedTriangleValue (τ : C(StdSimplex ℝ (Fin 3), Y))
    (hτ : ∀ i, τ (StdSimplex.single i) = y) : Additive (HomotopyGroup.Pi 2 Y y) :=
  Additive.ofMul (cappedTriangleSphereClass (ContinuousMap.id Y) (rfl : y = y) τ hτ
    (normalizedLoopCap y (sourceTriangleEdge τ hτ 0 1))
    (normalizedLoopCap y (sourceTriangleEdge τ hτ 1 2))
    (normalizedLoopCap y (sourceTriangleEdge τ hτ 0 2)))

private theorem normalizedCap_eq_spherical (a : SphericalSimplex Y y 2) (i j : Fin 3) :
    normalizedLoopCap y (sourceTriangleEdge a.val (sphericalTriangle_vertex a) i j) =
      sphericalTriangleCap a i j := by
  classical
  unfold normalizedLoopCap
  rw [dite_eq_left (sphericalTriangle_edge a i j)]
  rfl

private theorem normalizedLoopCap_cast {p q : Path y y} (hp : p = q) :
    normalizedLoopCap y p = (normalizedLoopCap y q).cast hp rfl := by
  subst q
  rfl

/-- The cap value marks the original spherical Pi-two representative with its original sign. -/
theorem basedTriangleValue_spherical (a : SphericalSimplex Y y 2) :
    basedTriangleValue y a.val (sphericalTriangle_vertex a) =
      Additive.ofMul a.homotopyClassStick := by
  unfold basedTriangleValue
  rw [normalizedCap_eq_spherical, normalizedCap_eq_spherical, normalizedCap_eq_spherical,
    cappedTriangleSphereClass_spherical]

/-- The literal constant triangle has zero value. -/
theorem basedTriangleValue_const :
    basedTriangleValue y (ContinuousMap.const _ y) (fun _ ↦ rfl) = 0 :=
  (basedTriangleValue_spherical y SphericalSimplex.const).trans
    (congrArg Additive.ofMul SphericalSimplex.homotopyClassStick_const)

/-- A face uses the same chosen null paths as its actual edges in the original tetrahedron. -/
theorem basedTriangleValue_tetrahedronFace
    (T : C(StdSimplex ℝ (Fin 4), Y)) (hT : ∀ i, T (StdSimplex.single i) = y)
    (i : Fin 4) :
    basedTriangleValue y (sourceTetrahedronFace T i) (sourceTetrahedronFace_vertex T hT i) =
      Additive.ofMul (tetrahedronFaceSphereClass (ContinuousMap.id Y) (rfl : y = y) T hT
        (fun j k _ ↦ normalizedLoopCap y (sourceTetrahedronEdge T hT j k)) i) := by
  have hcap (j k : Fin 3) (hjk : j < k) :
      normalizedLoopCap y
        (sourceTriangleEdge (sourceTetrahedronFace T i) (sourceTetrahedronFace_vertex T hT i) j k) =
      tetrahedronFaceCap (ContinuousMap.id Y) (rfl : y = y) T hT
        (fun a b _ ↦ normalizedLoopCap y (sourceTetrahedronEdge T hT a b)) i j k hjk := by
    exact normalizedLoopCap_cast y (sourceTriangleEdge_tetrahedronFace T hT i j k)
  unfold basedTriangleValue tetrahedronFaceSphereClass
  rw [hcap 0 1, hcap 1 2, hcap 0 2]

/-- The original ambient tetrahedron differential has zero cap value. -/
theorem basedTriangleValue_tetrahedral
    (T : C(StdSimplex ℝ (Fin 4), Y)) (hT : ∀ i, T (StdSimplex.single i) = y) :
    basedTriangleValue y (sourceTetrahedronFace T 0) (sourceTetrahedronFace_vertex T hT 0) -
      basedTriangleValue y (sourceTetrahedronFace T 1) (sourceTetrahedronFace_vertex T hT 1) +
      basedTriangleValue y (sourceTetrahedronFace T 2) (sourceTetrahedronFace_vertex T hT 2) -
      basedTriangleValue y (sourceTetrahedronFace T 3)
        (sourceTetrahedronFace_vertex T hT 3) = 0 := by
  have hc := ambient_cappedTetrahedron_cocycle y T hT
    (fun i j _ ↦ normalizedLoopCap y (sourceTetrahedronEdge T hT i j))
  rw [basedTriangleValue_tetrahedronFace, basedTriangleValue_tetrahedronFace,
    basedTriangleValue_tetrahedronFace, basedTriangleValue_tetrahedronFace]
  exact hc

end Topology.HomotopyFiber
