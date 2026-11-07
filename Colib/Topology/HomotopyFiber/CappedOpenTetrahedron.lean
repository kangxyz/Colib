/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.CappedOpenTriangle
public import Colib.Topology.HomotopyFiber.CappedTetrahedron
public import Colib.Topology.HomotopyFiber.ConnectingBasepointTransport
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransportFundamentalGroup

/-!
# Shared-cap tetrahedra with distinct source vertices

The six displayed edge caps produce paths between the four actual fiber
vertices. The face based at vertex one is transported along the reverse of
the actual capped edge 01. The original connecting map follows this path.
All remaining boundary cancellation takes place in the original fundamental
groupoid, with no assumption that the source vertices are equal.
-/

/-! Implementation source: `Quillen/Topology/HomotopyFiber/CappedOpenTetrahedron.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual fiber paths, source returns,
ordered face maps and signs are retained directly on native singular simplices. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory stdSimplex FundamentalGroupoid
open scoped Topology unitInterval
universe u

namespace Topology.HomotopyFiber

/-- The four actual triangle boundaries cancel after transporting face 123 along edge 01. -/
theorem path_tetrahedron_boundary_identity {Z : Type*} [TopologicalSpace Z]
    {z₀ z₁ z₂ z₃ : Z}
    (p₀₁ : Path z₀ z₁) (p₀₂ : Path z₀ z₂) (p₀₃ : Path z₀ z₃)
    (p₁₂ : Path z₁ z₂) (p₁₃ : Path z₁ z₃) (p₂₃ : Path z₂ z₃) :
    (Path.Homotopic.Quotient.mk
      ((p₀₁.trans ((p₁₂.trans p₂₃).trans p₁₃.symm)).trans p₀₁.symm)).trans
        (Path.Homotopic.Quotient.mk ((p₀₁.trans p₁₃).trans p₀₃.symm)) =
    (Path.Homotopic.Quotient.mk ((p₀₁.trans p₁₂).trans p₀₂.symm)).trans
      (Path.Homotopic.Quotient.mk ((p₀₂.trans p₂₃).trans p₀₃.symm)) := by
  let a₀₁ : FundamentalGroupoid.mk z₀ ⟶ FundamentalGroupoid.mk z₁ := ⟦p₀₁⟧
  let a₀₂ : FundamentalGroupoid.mk z₀ ⟶ FundamentalGroupoid.mk z₂ := ⟦p₀₂⟧
  let a₀₃ : FundamentalGroupoid.mk z₀ ⟶ FundamentalGroupoid.mk z₃ := ⟦p₀₃⟧
  let a₁₂ : FundamentalGroupoid.mk z₁ ⟶ FundamentalGroupoid.mk z₂ := ⟦p₁₂⟧
  let a₁₃ : FundamentalGroupoid.mk z₁ ⟶ FundamentalGroupoid.mk z₃ := ⟦p₁₃⟧
  let a₂₃ : FundamentalGroupoid.mk z₂ ⟶ FundamentalGroupoid.mk z₃ := ⟦p₂₃⟧
  change ((a₀₁ ≫ ((a₁₂ ≫ a₂₃) ≫ Groupoid.inv a₁₃)) ≫ Groupoid.inv a₀₁) ≫
      ((a₀₁ ≫ a₁₃) ≫ Groupoid.inv a₀₃) =
    ((a₀₁ ≫ a₁₂) ≫ Groupoid.inv a₀₂) ≫ ((a₀₂ ≫ a₂₃) ≫ Groupoid.inv a₀₃)
  simp only [Groupoid.inv_eq_inv, Category.assoc, IsIso.inv_hom_id_assoc]

/-- The original path transport has the literal transported boundary word in Pi one. -/
theorem piOne_transport_reverse_path {Z : Type*} [TopologicalSpace Z]
    {a b : Z} (p : Path a b) (q : Path b b) :
    HomotopyGroup.pi1MulEquivFundamentalGroup
      (pathTransport p.symm 1 (HomotopyGroup.pi1MulEquivFundamentalGroup.symm
        (⟦q⟧ : FundamentalGroup Z b))) =
      (⟦(p.trans q).trans p.symm⟧ : FundamentalGroup Z a) := by
  rw [piOneEquivFundamentalGroup_pathTransport, MulEquiv.apply_symm_apply]
  change (Path.Homotopic.Quotient.mk p.symm).symm.trans
    ((Path.Homotopic.Quotient.mk q).trans (Path.Homotopic.Quotient.mk p.symm)) =
      Path.Homotopic.Quotient.mk ((p.trans q).trans p.symm)
  rw [← Path.Homotopic.Quotient.mk_symm, Path.symm_symm]
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.trans_assoc]

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
variable (f : C(X, Y)) (y : Y)

/-- Equal original source points give equal original constant-path fiber vertices. -/
theorem basepoint_eq_of_source_eq {a b : X} (e : a = b) (ha : f a = y) (hb : f b = y) :
    basepoint f y a ha = basepoint f y b hb := by subst b; rfl

/-- Endpoint equality casts preserve the original connecting map and displayed fiber loop. -/
theorem connectingHom_class_of_source_eq {a b : X} (e : a = b)
    (ha : f a = y) (hb : f b = y) (c : HomotopyGroup.Pi 2 Y y)
    (q : Path (basepoint f y a ha) (basepoint f y a ha))
    (hq : connectingHom f y a ha 0 c = HomotopyGroup.pi1MulEquivFundamentalGroup.symm ⟦q⟧) :
    connectingHom f y b hb 0 c = HomotopyGroup.pi1MulEquivFundamentalGroup.symm
      ⟦q.cast (basepoint_eq_of_source_eq f y e ha hb).symm
        (basepoint_eq_of_source_eq f y e ha hb).symm⟧ := by
  subst b
  exact hq

variable (T : C(_root_.stdSimplex ℝ (Fin 4), X)) (hT : ∀ i, f (T (stdSimplex.vertex i)) = y)

/-- The actual source edge of the original tetrahedron, with distinct source endpoints. -/
def openTetrahedronEdge (i j : Fin 4) : Path (T (stdSimplex.vertex i)) (T (stdSimplex.vertex j)) :=
  (LocalCoefficients.simplexEdgePath i j).map T.continuous

/-- The original face evaluates to the original selected source vertex. -/
theorem openTetrahedronFace_vertex (i : Fin 4) (j : Fin 3) :
    sourceTetrahedronFace T i (stdSimplex.vertex j) = T (stdSimplex.vertex (i.succAbove j)) := by
  change T (stdSimplex.map i.succAbove (stdSimplex.vertex j)) = _
  rw [stdSimplex.map_vertex]

include hT in
/-- Only the images of the four vertices are based. -/
theorem openTetrahedronFace_image_vertex (i : Fin 4) (j : Fin 3) :
    f (sourceTetrahedronFace T i (stdSimplex.vertex j)) = y := by
  rw [openTetrahedronFace_vertex]
  exact hT _

/-- Every source face edge is exactly the corresponding original edge, with endpoint casts. -/
theorem openTriangleEdge_tetrahedronFace (i : Fin 4) (j k : Fin 3) :
    openTriangleEdge (sourceTetrahedronFace T i) j k =
      (openTetrahedronEdge T (i.succAbove j) (i.succAbove k)).cast
        (openTetrahedronFace_vertex T i j) (openTetrahedronFace_vertex T i k) := by
  ext t
  change T (stdSimplex.map i.succAbove (LocalCoefficients.simplexEdgePoint j k t)) =
    T (LocalCoefficients.simplexEdgePoint (i.succAbove j) (i.succAbove k) t)
  apply congrArg T
  unfold LocalCoefficients.simplexEdgePoint
  rw [stdSimplex.map_comp_apply]
  congr 1
  funext l
  simp only [Function.comp_apply]
  split_ifs <;> rfl

/-- Target endpoint casts retain the same original image loop under face restriction. -/
theorem basedImagePath_tetrahedronFace (i : Fin 4) (j k : Fin 3) :
    basedImagePath f y (openTetrahedronFace_image_vertex f y T hT i j)
      (openTetrahedronFace_image_vertex f y T hT i k)
      (openTriangleEdge (sourceTetrahedronFace T i) j k) =
    basedImagePath f y (hT (i.succAbove j)) (hT (i.succAbove k))
      (openTetrahedronEdge T (i.succAbove j) (i.succAbove k)) := by
  rw [openTriangleEdge_tetrahedronFace]
  rfl

variable (P : ∀ i j : Fin 4, i < j →
  Path (basedImagePath f y (hT i) (hT j) (openTetrahedronEdge T i j)) (Path.refl y))

/-- Each face uses the very same cap on its original increasing tetrahedron edge. -/
def openTetrahedronFaceCap (i : Fin 4) (j k : Fin 3) (hjk : j < k) :
    Path (basedImagePath f y (openTetrahedronFace_image_vertex f y T hT i j)
      (openTetrahedronFace_image_vertex f y T hT i k)
      (openTriangleEdge (sourceTetrahedronFace T i) j k)) (Path.refl y) :=
  (P (i.succAbove j) (i.succAbove k) (tetrahedronFace_edge_order i j k hjk)).cast
    (basedImagePath_tetrahedronFace f y T hT i j k) rfl

/-- The actual path between two original constant-path fiber vertices. -/
def openTetrahedronFiberEdge (i j : Fin 4) (hij : i < j) :
    Path (basepoint f y (T (stdSimplex.vertex i)) (hT i))
      (basepoint f y (T (stdSimplex.vertex j)) (hT j)) :=
  cappedPath f y (hT i) (hT j) (openTetrahedronEdge T i j) (P i j hij)

/-- The face sphere retains the actual face and its three original shared edge caps. -/
def openTetrahedronFaceSphereClass (i : Fin 4) : HomotopyGroup.Pi 2 Y y :=
  cappedOpenTriangleSphereClass f y (sourceTetrahedronFace T i)
    (openTetrahedronFace_image_vertex f y T hT i)
    (openTetrahedronFaceCap f y T hT P i 0 1 (by decide))
    (openTetrahedronFaceCap f y T hT P i 1 2 (by decide))
    (openTetrahedronFaceCap f y T hT P i 0 2 (by decide))

/-- The complete face fiber path is the original shared edge path, with only endpoint casts. -/
theorem cappedPath_openTetrahedronFaceCap (i : Fin 4) (j k : Fin 3) (hjk : j < k) :
    cappedPath f y (openTetrahedronFace_image_vertex f y T hT i j)
      (openTetrahedronFace_image_vertex f y T hT i k)
      (openTriangleEdge (sourceTetrahedronFace T i) j k)
      (openTetrahedronFaceCap f y T hT P i j k hjk) =
    (openTetrahedronFiberEdge f y T hT P (i.succAbove j) (i.succAbove k)
      (tetrahedronFace_edge_order i j k hjk)).cast
        (basepoint_eq_of_source_eq f y (openTetrahedronFace_vertex T i j) _ _)
        (basepoint_eq_of_source_eq f y (openTetrahedronFace_vertex T i k) _ _) := by
  ext s
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun p ↦ p s) (openTriangleEdge_tetrahedronFace T i j k)
  · rfl

/-- Each original connecting face image is its actual three-edge boundary at the original vertex. -/
theorem connectingHom_openTetrahedronFaceSphereClass (i : Fin 4) :
    connectingHom f y (T (stdSimplex.vertex (i.succAbove 0))) (hT (i.succAbove 0)) 0
      (openTetrahedronFaceSphereClass f y T hT P i) =
    HomotopyGroup.pi1MulEquivFundamentalGroup.symm
      ⟦((openTetrahedronFiberEdge f y T hT P (i.succAbove 0) (i.succAbove 1)
          (tetrahedronFace_edge_order i 0 1 (by decide))).trans
        (openTetrahedronFiberEdge f y T hT P (i.succAbove 1) (i.succAbove 2)
          (tetrahedronFace_edge_order i 1 2 (by decide)))).trans
      (openTetrahedronFiberEdge f y T hT P (i.succAbove 0) (i.succAbove 2)
          (tetrahedronFace_edge_order i 0 2 (by decide))).symm⟧ := by
  have hf := connectingHom_cappedOpenTriangleSphereClass f y (sourceTetrahedronFace T i)
    (openTetrahedronFace_image_vertex f y T hT i)
    (openTetrahedronFaceCap f y T hT P i 0 1 (by decide))
    (openTetrahedronFaceCap f y T hT P i 1 2 (by decide))
    (openTetrahedronFaceCap f y T hT P i 0 2 (by decide))
  have hg := connectingHom_class_of_source_eq f y (openTetrahedronFace_vertex T i 0)
    (openTetrahedronFace_image_vertex f y T hT i 0) (hT (i.succAbove 0)) _ _ hf
  refine hg.trans ?_
  apply congrArg HomotopyGroup.pi1MulEquivFundamentalGroup.symm
  apply congrArg Path.Homotopic.Quotient.mk
  rw [cappedPath_openTetrahedronFaceCap, cappedPath_openTetrahedronFaceCap,
    cappedPath_openTetrahedronFaceCap]
  ext t
  rfl

/-- The sphere of each open source face is exactly the sphere of the actual image face. -/
theorem openTetrahedronFaceSphereClass_image (i : Fin 4) :
    openTetrahedronFaceSphereClass f y T hT P i =
      tetrahedronFaceSphereClass (ContinuousMap.id Y) (rfl : y = y) (f.comp T) hT P i := by
  rfl

/-- The four exact shared-cap spheres satisfy the cocycle identity with distinct source vertices. -/
theorem cappedOpenTetrahedron_cocycle
    (hX : Subsingleton (HomotopyGroup.Pi 2 X (T (stdSimplex.vertex 0)))) :
    Additive.ofMul (openTetrahedronFaceSphereClass f y T hT P 0) -
      Additive.ofMul (openTetrahedronFaceSphereClass f y T hT P 1) +
      Additive.ofMul (openTetrahedronFaceSphereClass f y T hT P 2) -
      Additive.ofMul (openTetrahedronFaceSphereClass f y T hT P 3) = 0 := by
  let p₀₁ := openTetrahedronFiberEdge f y T hT P 0 1 (by decide)
  let p₀₂ := openTetrahedronFiberEdge f y T hT P 0 2 (by decide)
  let p₀₃ := openTetrahedronFiberEdge f y T hT P 0 3 (by decide)
  let p₁₂ := openTetrahedronFiberEdge f y T hT P 1 2 (by decide)
  let p₁₃ := openTetrahedronFiberEdge f y T hT P 1 3 (by decide)
  let p₂₃ := openTetrahedronFiberEdge f y T hT P 2 3 (by decide)
  let c := openTetrahedronFaceSphereClass f y T hT P
  let δ₀ := connectingHom f y (T (stdSimplex.vertex 0)) (hT 0) 0
  let δ₁ := connectingHom f y (T (stdSimplex.vertex 1)) (hT 1) 0
  let e₀ := HomotopyGroup.pi1MulEquivFundamentalGroup (X := HomotopyFiber f y)
    (x := basepoint f y (T (stdSimplex.vertex 0)) (hT 0))
  let e₁ := HomotopyGroup.pi1MulEquivFundamentalGroup (X := HomotopyFiber f y)
    (x := basepoint f y (T (stdSimplex.vertex 1)) (hT 1))
  have h₀ : δ₁ (c 0) = e₁.symm ⟦(p₁₂.trans p₂₃).trans p₁₃.symm⟧ :=
    connectingHom_openTetrahedronFaceSphereClass f y T hT P 0
  have h₁ : δ₀ (c 1) = e₀.symm ⟦(p₀₂.trans p₂₃).trans p₀₃.symm⟧ :=
    connectingHom_openTetrahedronFaceSphereClass f y T hT P 1
  have h₂ : δ₀ (c 2) = e₀.symm ⟦(p₀₁.trans p₁₃).trans p₀₃.symm⟧ :=
    connectingHom_openTetrahedronFaceSphereClass f y T hT P 2
  have h₃ : δ₀ (c 3) = e₀.symm ⟦(p₀₁.trans p₁₂).trans p₀₂.symm⟧ :=
    connectingHom_openTetrahedronFaceSphereClass f y T hT P 3
  have h₀' : e₀ (δ₀ (c 0)) =
      (⟦(p₀₁.trans ((p₁₂.trans p₂₃).trans p₁₃.symm)).trans p₀₁.symm⟧ :
        FundamentalGroup _ (basepoint f y (T (stdSimplex.vertex 0)) (hT 0))) := by
    have ht := pathTransport_connectingHom_zero f y (hT 1) (hT 0) p₀₁.symm (c 0)
    calc
      _ = e₀ (pathTransport p₀₁.symm 1 (δ₁ (c 0))) := congrArg e₀ ht.symm
      _ = e₀ (pathTransport p₀₁.symm 1 (e₁.symm ⟦(p₁₂.trans p₂₃).trans p₁₃.symm⟧)) := by
        rw [h₀]
      _ = _ := piOne_transport_reverse_path p₀₁ ((p₁₂.trans p₂₃).trans p₁₃.symm)
  have hδ : δ₀ (c 2 * c 0) = δ₀ (c 1 * c 3) := by
    apply e₀.injective
    simp only [map_mul]
    rw [h₂, h₁, h₃]
    simp only [MulEquiv.apply_symm_apply, h₀']
    exact path_tetrahedron_boundary_identity p₀₁ p₀₂ p₀₃ p₁₂ p₁₃ p₂₃
  have he := connectingHom_zero_injective_of_subsingleton_piTwo f (hT 0) hX hδ
  have he' : Additive.ofMul (c 2) + Additive.ofMul (c 0) =
      Additive.ofMul (c 1) + Additive.ofMul (c 3) := congrArg Additive.ofMul he
  change Additive.ofMul (c 0) - Additive.ofMul (c 1) +
    Additive.ofMul (c 2) - Additive.ofMul (c 3) = 0
  calc
    _ = (Additive.ofMul (c 2) + Additive.ofMul (c 0)) -
        (Additive.ofMul (c 1) + Additive.ofMul (c 3)) := by abel
    _ = 0 := by rw [he', sub_self]

end Topology.HomotopyFiber
