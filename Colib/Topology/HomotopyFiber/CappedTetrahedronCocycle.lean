/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.CappedOpenTetrahedron
public import Colib.Topology.Realization.SimplexConnectivity
public import Colib.Topology.Homotopy.HomotopyGroup.Contractible

/-!
# The ambient target tetrahedron cocycle for the original cap spheres

Use the actual universe-lifted standard three-simplex as the source of the
given ambient singular tetrahedron. Its proved contractibility makes the
original connecting map injective. Open capped edges give the necessary
paths between its four actual fiber vertices. The image-face identities
return exactly the original ambient face spheres and the original six caps.
No source-image assumption on the ambient tetrahedron is made.
-/

/-! Implementation source: `Quillen/Topology/HomotopyFiber/CappedTetrahedronCocycle.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual fiber paths, source returns,
ordered face maps and signs are retained directly on native singular simplices. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open scoped Topology
open stdSimplex FundamentalGroupoid
universe u

namespace Topology.HomotopyFiber
variable {Y : Type u} [TopologicalSpace Y]

/-- The four original ambient faces have zero alternating cap-sphere sum.
The six supplied null caps are shared through the actual increasing face maps. -/
theorem ambient_cappedTetrahedron_cocycle (y : Y)
    (T : C(_root_.stdSimplex ℝ (Fin 4), Y)) (hT : ∀ i, T (stdSimplex.vertex i) = y)
    (P : ∀ i j : Fin 4, i < j →
      Path (basedLoopMap (ContinuousMap.id Y) (rfl : y = y)
        (sourceTetrahedronEdge T hT i j)) (Path.refl y)) :
    Additive.ofMul (tetrahedronFaceSphereClass (ContinuousMap.id Y) (rfl : y = y) T hT P 0) -
      Additive.ofMul (tetrahedronFaceSphereClass (ContinuousMap.id Y) (rfl : y = y) T hT P 1) +
      Additive.ofMul (tetrahedronFaceSphereClass (ContinuousMap.id Y) (rfl : y = y) T hT P 2) -
      Additive.ofMul (tetrahedronFaceSphereClass (ContinuousMap.id Y)
        (rfl : y = y) T hT P 3) = 0 := by
  let D := ULift.{u} (_root_.stdSimplex ℝ (Fin 4))
  let : ContractibleSpace (_root_.stdSimplex ℝ (Fin 4)) := stdSimplex.contractibleSpace (Fin 4)
  let : ContractibleSpace D :=
    (Homeomorph.ulift : D ≃ₜ _root_.stdSimplex ℝ (Fin 4)).contractibleSpace
  let F : C(D, Y) := ⟨fun z : ULift.{u} (_root_.stdSimplex ℝ (Fin 4)) ↦ T z.down, by fun_prop⟩
  let S : C(_root_.stdSimplex ℝ (Fin 4), D) := ⟨ULift.up, by fun_prop⟩
  have hS : ∀ i, F (S (stdSimplex.vertex i)) = y := hT
  have hc := cappedOpenTetrahedron_cocycle F y S hS P
    (subsingleton_pi_of_contractible 2 D (S (stdSimplex.vertex 0)))
  simp only [openTetrahedronFaceSphereClass_image] at hc
  have he (i : Fin 4) :
      tetrahedronFaceSphereClass (ContinuousMap.id Y) (rfl : y = y) (F.comp S) hS P i =
        tetrahedronFaceSphereClass (ContinuousMap.id Y) (rfl : y = y) T hT P i := by
    rfl
  rw [he 0, he 1, he 2, he 3] at hc
  exact hc

end Topology.HomotopyFiber
