/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.FiniteCapEvaluation

/-!
# The original connecting cap value is a source coboundary

Each actual based source edge gives its original capped fiber-loop class in
the abelianization of the actual fiber Pi one. The proved source-triangle
identity identifies the connecting image of the original image triangle
with its alternating source-edge values. Finite endpoint assignments retain
this identity on the original source support through actual face compatibility.
-/

/-! Implementation source: `Quillen/Topology/LocalCoefficients/SourceCapCoboundary.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual native singular chains,
ordered cap evaluation and original connecting homomorphism are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits Topology Convexity.StdSimplex
open scoped Simplicial Topology
universe u

namespace FundamentalGroupoid.LocalCoefficients
open HomotopyFiber
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
variable [SimplyConnectedSpace Y] (f : C(X, Y)) (x : X)

/-- The original connecting map followed by the original abelianization, in additive notation. -/
def connectingAbelianization : Additive (HomotopyGroup.Pi 2 Y (f x)) →+
    Additive (Abelianization (HomotopyGroup.Pi 1 (HomotopyFiber f (f x))
      (HomotopyFiber.basepoint f (f x) x rfl))) :=
  (Abelianization.of.comp (connectingHom f (f x) x rfl 0)).toAdditive

/-- The original capped source loop value with the shared normalized target cap. -/
def sourceLoopCapValue (p : Path x x) :
    Additive (Abelianization (HomotopyGroup.Pi 1 (HomotopyFiber f (f x))
      (HomotopyFiber.basepoint f (f x) x rfl))) :=
  abelianCappedLoopValue f rfl p (normalizedLoopCap (f x) (basedLoopMap f rfl p))

/-- The image-triangle cap uses the original map and the same normalized edge caps. -/
theorem sourceTriangle_cap_coboundary
    (τ : SingularSimplex X ⦋2⦌) (hτ : SimplexVerticesAt x τ) :
    connectingAbelianization f x (basedTriangleValue (f x) (f.comp τ)
      (fun i ↦ congrArg f (hτ i))) =
      sourceLoopCapValue f x (sourceTriangleEdge τ hτ 1 2) -
        sourceLoopCapValue f x (sourceTriangleEdge τ hτ 0 2) +
          sourceLoopCapValue f x (sourceTriangleEdge τ hτ 0 1) := by
  have he := abelian_connecting_cappedTriangleSphereClass f (rfl : f x = f x) τ hτ
    (normalizedLoopCap (f x) (basedLoopMap f rfl (sourceTriangleEdge τ hτ 0 1)))
    (normalizedLoopCap (f x) (basedLoopMap f rfl (sourceTriangleEdge τ hτ 1 2)))
    (normalizedLoopCap (f x) (basedLoopMap f rfl (sourceTriangleEdge τ hτ 0 2)))
  rw [cappedTriangleSphereClass_image] at he
  exact he

/-- Traverse the actual one-simplex from its first original vertex to its second. -/
def basedOneSimplexPath (τ : SingularSimplex X ⦋1⦌) (hτ : SimplexVerticesAt x τ) : Path x x :=
  ((simplexEdgePath 0 1).map τ.continuous).cast (hτ 0).symm (hτ 1).symm

/-- Actual increasing face restriction preserves the original edge path and its parameter. -/
theorem basedOneSimplexPath_triangleFace (τ : SingularSimplex X ⦋2⦌)
    (hτ : SimplexVerticesAt x τ) (i : Fin 3) :
    basedOneSimplexPath x (restrictSimplex τ (SimplexCategory.δ i)) (hτ.face i) =
      sourceTriangleEdge τ hτ (i.succAbove 0) (i.succAbove 1) := by
  ext t
  change τ (Convexity.StdSimplex.map i.succAbove (simplexEdgePoint 0 1 t)) =
    τ (simplexEdgePoint (i.succAbove 0) (i.succAbove 1) t)
  apply congrArg τ
  unfold simplexEdgePoint
  rw [← Convexity.StdSimplex.map_comp]
  congr 1
  funext j
  simp only [Function.comp_apply]
  split_ifs <;> rfl

/-- The cap value of the original based one-simplex. -/
def basedOneCapValue (τ : SingularSimplex X ⦋1⦌) (hτ : SimplexVerticesAt x τ) :
    Additive (Abelianization (HomotopyGroup.Pi 1 (HomotopyFiber f (f x))
      (HomotopyFiber.basepoint f (f x) x rfl))) :=
  sourceLoopCapValue f x (basedOneSimplexPath x τ hτ)

/-- Equality of actual one-simplex maps is enough; proofs of their vertex values do not matter. -/
theorem basedOneCapValue_congr {a b : SingularSimplex X ⦋1⦌} (e : a = b)
    (ha : SimplexVerticesAt x a) (hb : SimplexVerticesAt x b) :
    basedOneCapValue f x a ha = basedOneCapValue f x b hb := by subst b; rfl

variable {S F : FiniteSimplexFamily X} {hS : S.FaceClosed} {N : ℕ}

/-- The finite source-edge assignment extends by zero on unselected original one-simplices. -/
def finiteOneCapValue (R : PartialSimplexStraightening 1 x S F hS N) (hN : 1 < N)
    (τ : SingularSimplex X ⦋1⦌) :
    Additive (Abelianization (HomotopyGroup.Pi 1 (HomotopyFiber f (f x))
      (HomotopyFiber.basepoint f (f x) x rfl))) := by
  classical
  exact if hτ : τ ∈ S 1 then basedOneCapValue f x (R.endpoint 1 ⟨τ, hτ⟩)
    (R.endpoint_vertices 1 hN ⟨τ, hτ⟩) else 0

/-- A selected original face evaluates at the corresponding actual endpoint face. -/
theorem finiteOneCapValue_triangleFace
    (R : PartialSimplexStraightening 1 x S F hS N) (hN : 2 < N)
    (τ : {τ // τ ∈ S 2}) (i : Fin 3) :
    finiteOneCapValue f x R (by omega) (restrictSimplex τ.val (SimplexCategory.δ i)) =
      basedOneCapValue f x (restrictSimplex (R.endpoint 2 τ) (SimplexCategory.δ i))
        (SimplexVerticesAt.face (R.endpoint_vertices 2 hN τ) i) := by
  classical
  change finiteOneCapValue f x R (by omega) (hS.face τ i).val = _
  rw [finiteOneCapValue, dite_eq_left (hS.face τ i).property]
  exact basedOneCapValue_congr f x (R.endpoint_face 1 hN τ i).symm _ _

/-- The connecting cap of an actual source endpoint is the original finite edge coboundary. -/
theorem finite_sourceTriangle_cap_coboundary
    (R : PartialSimplexStraightening 1 x S F hS N) (hN : 2 < N)
    (τ : {τ // τ ∈ S 2}) (b : ULift.{u} ℤ) :
    connectingAbelianization f x
      (b.down • basedTriangleValue (f x) (f.comp (R.endpoint 2 τ))
        (fun i ↦ congrArg f (R.endpoint_vertices 2 hN τ i))) =
    integralChainEvaluation 1 (finiteOneCapValue f x R (by omega))
      ((singularChainComplex (constant X integralCoefficients.{u})).d 2 1
        (chainInclusion (constant X integralCoefficients.{u}) τ.val b)) := by
  rw [map_zsmul, sourceTriangle_cap_coboundary f x (R.endpoint 2 τ)
    (R.endpoint_vertices 2 hN τ), integralChainEvaluation_boundary]
  have hface (i : Fin 3) : finiteOneCapValue f x R (by omega)
      (restrictSimplex τ.val (SimplexCategory.δ i)) =
      sourceLoopCapValue f x
        (sourceTriangleEdge (R.endpoint 2 τ) (R.endpoint_vertices 2 hN τ)
          (i.succAbove 0) (i.succAbove 1)) :=
    (finiteOneCapValue_triangleFace f x R hN τ i).trans
      (congrArg (sourceLoopCapValue f x)
        (basedOneSimplexPath_triangleFace x (R.endpoint 2 τ) (R.endpoint_vertices 2 hN τ) i))
  simp only [hface]
  simp [Fin.sum_univ_succ, sub_eq_add_neg, smul_add, smul_neg, add_assoc]

end FundamentalGroupoid.LocalCoefficients
