/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.CappedTriangle
public import Colib.Topology.HomotopyFiber.LoopCentrality

/-!
# The exact shared-cap source tetrahedron cocycle

The six increasing edges of one actual source tetrahedron supply one cap each.
Its four face caps are restrictions of these same six paths, through proved
equalities of actual singular edges. Centrality of the original connecting
image and associativity give the four-defect relation. When the actual source
Pi two vanishes, the original LES makes the connecting map injective, giving
the exact alternating tetrahedral cocycle in the original target Pi two.

This statement concerns a source tetrahedron; ambient target tetrahedra still
require their own source representation and cap/basepoint comparison.
-/

/-! Implementation source: `Quillen/Topology/HomotopyFiber/CappedTetrahedron.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual fiber paths, source returns,
ordered face maps and signs are retained directly on native singular simplices. -/
@[expose] public section

open Convexity
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
open StdSimplex FundamentalGroupoid
universe u

namespace Topology.HomotopyFiber

/-- Associativity gives the four-defect equation with the actual ordered edge products. -/
theorem central_triangle_defects {G : Type*} [Group G]
    (a₀₁ a₀₂ a₀₃ a₁₂ a₁₃ a₂₃ : G)
    (hc : Commute a₀₁ (a₁₃⁻¹ * (a₂₃ * a₁₂))) :
    (a₀₃⁻¹ * (a₁₃ * a₀₁)) * (a₁₃⁻¹ * (a₂₃ * a₁₂)) =
      (a₀₃⁻¹ * (a₂₃ * a₀₂)) * (a₀₂⁻¹ * (a₁₂ * a₀₁)) := by
  calc
    _ = a₀₃⁻¹ * (a₁₃ * (a₀₁ * (a₁₃⁻¹ * (a₂₃ * a₁₂)))) := by
      simp only [mul_assoc]
    _ = a₀₃⁻¹ * (a₁₃ * ((a₁₃⁻¹ * (a₂₃ * a₁₂)) * a₀₁)) := by rw [hc.eq]
    _ = _ := by group

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
variable (f : C(X, Y)) {x : X} {y : Y} (h : f x = y)

/-- Vanishing of the actual source Pi two makes the original connecting map injective. -/
theorem connectingHom_zero_injective_of_subsingleton_piTwo
    (hX : Subsingleton (HomotopyGroup.Pi 2 X x)) :
    Function.Injective (connectingHom f y x h 0) := by
  let := hX
  intro a b hab
  have hz : connectingHom f y x h 0 (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  have hm : a * b⁻¹ ∈ (HomotopyGroup.piMap 1 f h).range := by
    rw [range_piMap_eq_ker_connectingHom f y x h 0]
    exact hz
  obtain ⟨c, hc⟩ := hm
  have hc₁ : c = 1 := Subsingleton.elim _ _
  have hab₁ : a * b⁻¹ = 1 := by rw [← hc, hc₁, map_one]
  exact mul_inv_eq_one.mp hab₁

variable (T : C(StdSimplex ℝ (Fin 4), X)) (hT : ∀ i, T (StdSimplex.single i) = x)

/-- Each increasing tetrahedron edge is the actual standard simplex edge. -/
def sourceTetrahedronEdge (i j : Fin 4) : Path x x :=
  ((LocalCoefficients.simplexEdgePath i j).map T.continuous).cast (hT i).symm (hT j).symm

/-- The original increasing-vertex face, with no replacement triangle. -/
def sourceTetrahedronFace (i : Fin 4) : C(StdSimplex ℝ (Fin 3), X) :=
  T.comp ⟨StdSimplex.map i.succAbove, StdSimplex.continuous_map ℝ _⟩

include hT in
/-- Every face vertex is the corresponding original tetrahedron vertex. -/
theorem sourceTetrahedronFace_vertex (i : Fin 4) (j : Fin 3) :
    sourceTetrahedronFace T i (StdSimplex.single j) = x := by
  change T (StdSimplex.map i.succAbove (StdSimplex.single j)) = x
  simpa only [StdSimplex.map_single] using hT (i.succAbove j)

/-- Face restriction preserves the complete original edge parameter. -/
theorem sourceTriangleEdge_tetrahedronFace (i : Fin 4) (j k : Fin 3) :
    sourceTriangleEdge (sourceTetrahedronFace T i) (sourceTetrahedronFace_vertex T hT i) j k =
      sourceTetrahedronEdge T hT (i.succAbove j) (i.succAbove k) := by
  ext t
  change T (StdSimplex.map i.succAbove (LocalCoefficients.simplexEdgePoint j k t)) =
    T (LocalCoefficients.simplexEdgePoint (i.succAbove j) (i.succAbove k) t)
  apply congrArg T
  unfold LocalCoefficients.simplexEdgePoint
  rw [StdSimplex.map_map]
  congr 1
  funext l
  split_ifs <;> rfl

/-- The actual increasing face map preserves the order of each selected edge. -/
theorem tetrahedronFace_edge_order (i : Fin 4) (j k : Fin 3) (hjk : j < k) :
    i.succAbove j < i.succAbove k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num at * <;> decide

variable (P : ∀ i j : Fin 4, i < j →
  Path (basedLoopMap f h (sourceTetrahedronEdge T hT i j)) (Path.refl y))

/-- A face cap is the original shared tetrahedron-edge cap, changing only endpoint proofs. -/
def tetrahedronFaceCap (i : Fin 4) (j k : Fin 3) (hjk : j < k) :
    Path (basedLoopMap f h
      (sourceTriangleEdge (sourceTetrahedronFace T i) (sourceTetrahedronFace_vertex T hT i) j k))
      (Path.refl y) :=
  (P (i.succAbove j) (i.succAbove k) (tetrahedronFace_edge_order i j k hjk)).cast
    (congrArg (basedLoopMap f h) (sourceTriangleEdge_tetrahedronFace T hT i j k)) rfl

/-- The class of one of the six original capped source edges. -/
def tetrahedronEdgeClass (i j : Fin 4) (hij : i < j) :
    HomotopyGroup.Pi 1 (HomotopyFiber f y) (basepoint f y x h) :=
  cappedLoopClass f h (sourceTetrahedronEdge T hT i j) (P i j hij)

/-- Each face sphere uses exactly its three restrictions of the six shared caps. -/
def tetrahedronFaceSphereClass (i : Fin 4) : HomotopyGroup.Pi 2 Y y :=
  cappedTriangleSphereClass f h (sourceTetrahedronFace T i) (sourceTetrahedronFace_vertex T hT i)
    (tetrahedronFaceCap f h T hT P i 0 1 (by decide))
    (tetrahedronFaceCap f h T hT P i 1 2 (by decide))
    (tetrahedronFaceCap f h T hT P i 0 2 (by decide))

private theorem cappedLoopClass_cast {p q : Path x x} (hp : p = q)
    (Q : Path (basedLoopMap f h q) (Path.refl y)) :
    cappedLoopClass f h p (Q.cast (congrArg (basedLoopMap f h) hp) rfl) =
      cappedLoopClass f h q Q := by
  subst q
  rfl

/-- The actual edge restriction, including the original cap, has its original fiber-loop class. -/
theorem cappedLoopClass_tetrahedronFaceCap (i : Fin 4) (j k : Fin 3) (hjk : j < k) :
    cappedLoopClass f h
      (sourceTriangleEdge (sourceTetrahedronFace T i) (sourceTetrahedronFace_vertex T hT i) j k)
      (tetrahedronFaceCap f h T hT P i j k hjk) =
    tetrahedronEdgeClass f h T hT P (i.succAbove j) (i.succAbove k)
      (tetrahedronFace_edge_order i j k hjk) :=
  cappedLoopClass_cast f h (sourceTriangleEdge_tetrahedronFace T hT i j k) _

/-- The original connecting map of each face is its ordered defect in the shared edge classes. -/
theorem connectingHom_tetrahedronFaceSphereClass (i : Fin 4) :
    connectingHom f y x h 0 (tetrahedronFaceSphereClass f h T hT P i) =
      (tetrahedronEdgeClass f h T hT P (i.succAbove 0) (i.succAbove 2)
        (tetrahedronFace_edge_order i 0 2 (by decide)))⁻¹ *
      (tetrahedronEdgeClass f h T hT P (i.succAbove 1) (i.succAbove 2)
        (tetrahedronFace_edge_order i 1 2 (by decide)) *
      tetrahedronEdgeClass f h T hT P (i.succAbove 0) (i.succAbove 1)
        (tetrahedronFace_edge_order i 0 1 (by decide))) := by
  rw [tetrahedronFaceSphereClass, connectingHom_cappedTriangleSphereClass]
  rw [cappedLoopClass_tetrahedronFaceCap, cappedLoopClass_tetrahedronFaceCap,
    cappedLoopClass_tetrahedronFaceCap]

/-- The exact shared-cap tetrahedral cocycle in original target Pi two.
Only actual source Pi-two vanishing is used to make the existing connecting map injective. -/
theorem cappedTetrahedron_cocycle
    (hX : Subsingleton (HomotopyGroup.Pi 2 X x)) :
    Additive.ofMul (tetrahedronFaceSphereClass f h T hT P 0) -
      Additive.ofMul (tetrahedronFaceSphereClass f h T hT P 1) +
      Additive.ofMul (tetrahedronFaceSphereClass f h T hT P 2) -
      Additive.ofMul (tetrahedronFaceSphereClass f h T hT P 3) = 0 := by
  let a₀₁ := tetrahedronEdgeClass f h T hT P 0 1 (by decide)
  let a₀₂ := tetrahedronEdgeClass f h T hT P 0 2 (by decide)
  let a₀₃ := tetrahedronEdgeClass f h T hT P 0 3 (by decide)
  let a₁₂ := tetrahedronEdgeClass f h T hT P 1 2 (by decide)
  let a₁₃ := tetrahedronEdgeClass f h T hT P 1 3 (by decide)
  let a₂₃ := tetrahedronEdgeClass f h T hT P 2 3 (by decide)
  let c := tetrahedronFaceSphereClass f h T hT P
  let δ := connectingHom f y x h 0
  have h₀ : δ (c 0) = a₁₃⁻¹ * (a₂₃ * a₁₂) :=
    connectingHom_tetrahedronFaceSphereClass f h T hT P 0
  have h₁ : δ (c 1) = a₀₃⁻¹ * (a₂₃ * a₀₂) :=
    connectingHom_tetrahedronFaceSphereClass f h T hT P 1
  have h₂ : δ (c 2) = a₀₃⁻¹ * (a₁₃ * a₀₁) :=
    connectingHom_tetrahedronFaceSphereClass f h T hT P 2
  have h₃ : δ (c 3) = a₀₂⁻¹ * (a₁₂ * a₀₁) :=
    connectingHom_tetrahedronFaceSphereClass f h T hT P 3
  have hc : Commute a₀₁ (a₁₃⁻¹ * (a₂₃ * a₁₂)) := by
    rw [← h₀]
    exact Subgroup.mem_center_iff.mp (range_connectingHom_zero_le_center f y x h
      ⟨c 0, rfl⟩) a₀₁
  have hδ : δ (c 2 * c 0) = δ (c 1 * c 3) := by
    rw [map_mul, map_mul, h₀, h₁, h₂, h₃]
    exact central_triangle_defects a₀₁ a₀₂ a₀₃ a₁₂ a₁₃ a₂₃ hc
  have he := connectingHom_zero_injective_of_subsingleton_piTwo f h hX hδ
  have he' : Additive.ofMul (c 2) + Additive.ofMul (c 0) =
      Additive.ofMul (c 1) + Additive.ofMul (c 3) := congrArg Additive.ofMul he
  change Additive.ofMul (c 0) - Additive.ofMul (c 1) +
    Additive.ofMul (c 2) - Additive.ofMul (c 3) = 0
  calc
    _ = (Additive.ofMul (c 2) + Additive.ofMul (c 0)) -
        (Additive.ofMul (c 1) + Additive.ofMul (c 3)) := by abel
    _ = 0 := by rw [he', sub_self]

end Topology.HomotopyFiber
