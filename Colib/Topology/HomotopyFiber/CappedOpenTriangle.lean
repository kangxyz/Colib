/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.CappedTriangle

/-!
# Capped paths and source triangles with distinct source vertices

Only the images of the vertices are required to be the target basepoint.
An image cap of an actual source edge gives an actual path between its two
constant-path fiber vertices. The original capped-loop return then identifies
the connecting image of a triangle sphere with its actual three-edge fiber
boundary. The sphere agrees exactly with the construction on the image triangle.
-/

/-! Implementation source: `Quillen/Topology/HomotopyFiber/CappedOpenTriangle.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual fiber paths, source returns,
ordered face maps and signs are retained directly on native singular simplices. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
open stdSimplex FundamentalGroupoid
universe u

namespace Topology.HomotopyFiber
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
variable (f : C(X, Y)) (y : Y)

/-- The original image of a path with its two displayed target-basepoint equalities. -/
def basedImagePath {a b : X} (ha : f a = y) (hb : f b = y) (p : Path a b) : Path y y :=
  (p.map f.continuous).cast ha.symm hb.symm

/-- A target image cap gives an actual path between the two original fiber vertices. -/
def cappedPath {a b : X} (ha : f a = y) (hb : f b = y) (p : Path a b)
    (P : Path (basedImagePath f y ha hb p) (Path.refl y)) :
    Path (basepoint f y a ha) (basepoint f y b hb) where
  toFun s := ⟨(p s, ⟨fun t ↦ P t s, by fun_prop⟩),
    congrArg (fun q : Path y y ↦ q s) P.source,
    congrArg (fun q : Path y y ↦ q s) P.target⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk p.continuous
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : unitInterval × unitInterval ↦ P z.2 z.1)
    fun_prop
  source' := by
    apply Subtype.ext
    apply Prod.ext p.source
    exact ContinuousMap.ext (fun t ↦ (P t).source)
  target' := by
    apply Subtype.ext
    apply Prod.ext p.target
    exact ContinuousMap.ext (fun t ↦ (P t).target)

/-- The complete stored cap parameter is unchanged. -/
@[simp] theorem cappedPath_path {a b : X} (ha : f a = y) (hb : f b = y) (p : Path a b)
    (P : Path (basedImagePath f y ha hb p) (Path.refl y)) (s t : unitInterval) :
    (cappedPath f y ha hb p P s).val.2 t = P t s := rfl

/-- At a single source point, this is exactly the frozen original capped-loop construction. -/
theorem cappedPath_loop {a : X} (ha : f a = y) (p : Path a a)
    (P : Path (basedLoopMap f ha p) (Path.refl y)) :
    cappedPath f y ha ha p P = cappedLoop f ha p P := by ext t; rfl

/-- Original image concatenation retains both endpoint identifications. -/
theorem basedImagePath_trans {a b c : X} (ha : f a = y) (hb : f b = y) (hc : f c = y)
    (p : Path a b) (q : Path b c) :
    basedImagePath f y ha hc (p.trans q) =
      (basedImagePath f y ha hb p).trans (basedImagePath f y hb hc q) := by
  unfold basedImagePath
  rw [Path.map_trans]
  rfl

/-- The two edge caps concatenate spatially, with the same null-path time. -/
def cappedPathTransNull {a b c : X} (ha : f a = y) (hb : f b = y) (hc : f c = y)
    (p : Path a b) (q : Path b c)
    (P : Path (basedImagePath f y ha hb p) (Path.refl y))
    (Q : Path (basedImagePath f y hb hc q) (Path.refl y)) :
    Path (basedImagePath f y ha hc (p.trans q)) (Path.refl y) :=
  ((P.prod Q).map Path.continuous_trans).cast (basedImagePath_trans f y ha hb hc p q)
    Path.refl_trans_refl.symm

/-- The cap of the two-edge word is exactly the concatenation of the actual fiber paths. -/
theorem cappedPath_trans {a b c : X} (ha : f a = y) (hb : f b = y) (hc : f c = y)
    (p : Path a b) (q : Path b c)
    (P : Path (basedImagePath f y ha hb p) (Path.refl y))
    (Q : Path (basedImagePath f y hb hc q) (Path.refl y)) :
    cappedPath f y ha hc (p.trans q) (cappedPathTransNull f y ha hb hc p q P Q) =
      (cappedPath f y ha hb p P).trans (cappedPath f y hb hc q Q) := by
  ext s
  apply Subtype.ext
  apply Prod.ext
  · change (p.trans q) s = _
    simp only [Path.trans, Path.coe_mk_mk, Function.comp_apply]
    split_ifs <;> rfl
  · apply ContinuousMap.ext
    intro t
    change ((P t).trans (Q t)) s = _
    simp only [Path.trans, Path.coe_mk_mk, Function.comp_apply]
    split_ifs <;> rfl

/-- Reverse the original edge and every image loop in its cap. -/
def cappedPathSymmNull {a b : X} (ha : f a = y) (hb : f b = y) (p : Path a b)
    (P : Path (basedImagePath f y ha hb p) (Path.refl y)) :
    Path (basedImagePath f y hb ha p.symm) (Path.refl y) :=
  (P.map Path.continuous_symm).cast (by ext t; rfl) (by ext t; rfl)

/-- Reversal is literally reversal of the original fiber path. -/
theorem cappedPath_symm {a b : X} (ha : f a = y) (hb : f b = y) (p : Path a b)
    (P : Path (basedImagePath f y ha hb p) (Path.refl y)) :
    cappedPath f y hb ha p.symm (cappedPathSymmNull f y ha hb p P) =
      (cappedPath f y ha hb p P).symm := by ext t; rfl

variable (τ : C(_root_.stdSimplex ℝ (Fin 3), X))

/-- An original source edge with its distinct original endpoints. -/
def openTriangleEdge (i j : Fin 3) : Path (τ (stdSimplex.vertex i)) (τ (stdSimplex.vertex j)) :=
  (LocalCoefficients.simplexEdgePath i j).map τ.continuous

/-- The actual three-edge source boundary, based at its first source vertex. -/
def openTriangleBoundary : Path (τ (stdSimplex.vertex 0)) (τ (stdSimplex.vertex 0)) :=
  ((openTriangleEdge τ 0 1).trans (openTriangleEdge τ 1 2)).trans (openTriangleEdge τ 0 2).symm

/-- The complete source nullhomotopy is the original standard-simplex contraction. -/
def openTriangleReturn : Path (openTriangleBoundary τ) (Path.refl (τ (stdSimplex.vertex 0))) := by
  let H := (stdSimplex.pathHomotopy standardTriangleBoundary
    (Path.refl (stdSimplex.vertex 0))).map τ
  apply LoopComponentTransport.pathOfPathHomotopy
  exact H.cast (by
    rw [standardTriangleBoundary, Path.map_trans, Path.map_trans, ← Path.map_symm]
    rfl) (by ext t; rfl)

variable (hτ : ∀ i, f (τ (stdSimplex.vertex i)) = y)
  (P₀₁ : Path (basedImagePath f y (hτ 0) (hτ 1) (openTriangleEdge τ 0 1)) (Path.refl y))
  (P₁₂ : Path (basedImagePath f y (hτ 1) (hτ 2) (openTriangleEdge τ 1 2)) (Path.refl y))
  (P₀₂ : Path (basedImagePath f y (hτ 0) (hτ 2) (openTriangleEdge τ 0 2)) (Path.refl y))

/-- The full boundary cap is assembled from the three original open-edge caps. -/
def cappedOpenTriangleNull :
    Path (basedLoopMap f (hτ 0) (openTriangleBoundary τ)) (Path.refl y) :=
  cappedPathTransNull f y (hτ 0) (hτ 2) (hτ 0)
    ((openTriangleEdge τ 0 1).trans (openTriangleEdge τ 1 2)) (openTriangleEdge τ 0 2).symm
    (cappedPathTransNull f y (hτ 0) (hτ 1) (hτ 2) _ _ P₀₁ P₁₂)
    (cappedPathSymmNull f y (hτ 0) (hτ 2) _ P₀₂)

/-- The concrete sphere at the shared target point, retaining the original source triangle. -/
def cappedOpenTriangleSphereClass : HomotopyGroup.Pi 2 Y y :=
  cappedLoopSphereClass f (hτ 0) (openTriangleBoundary τ)
    (cappedOpenTriangleNull f y τ hτ P₀₁ P₁₂ P₀₂) (openTriangleReturn τ)

/-- The open-source construction is exactly the frozen construction on its actual image triangle. -/
theorem cappedOpenTriangleSphereClass_image :
    cappedOpenTriangleSphereClass f y τ hτ P₀₁ P₁₂ P₀₂ =
      cappedTriangleSphereClass (ContinuousMap.id Y) (rfl : y = y) (f.comp τ) hτ
        P₀₁ P₁₂ P₀₂ := by
  rfl

/-- The original connecting image is the actual three-edge fiber boundary at the first vertex. -/
theorem connectingHom_cappedOpenTriangleSphereClass :
    connectingHom f y (τ (stdSimplex.vertex 0)) (hτ 0) 0
      (cappedOpenTriangleSphereClass f y τ hτ P₀₁ P₁₂ P₀₂) =
    HomotopyGroup.pi1MulEquivFundamentalGroup.symm
      ⟦((cappedPath f y (hτ 0) (hτ 1) (openTriangleEdge τ 0 1) P₀₁).trans
        (cappedPath f y (hτ 1) (hτ 2) (openTriangleEdge τ 1 2) P₁₂)).trans
          (cappedPath f y (hτ 0) (hτ 2) (openTriangleEdge τ 0 2) P₀₂).symm⟧ := by
  rw [cappedOpenTriangleSphereClass, connectingHom_cappedLoopSphereClass]
  unfold cappedLoopClass
  apply congrArg HomotopyGroup.pi1MulEquivFundamentalGroup.symm
  apply congrArg Path.Homotopic.Quotient.mk
  rw [← cappedPath_loop]
  change cappedPath f y _ _ _ (cappedPathTransNull f y _ _ _ _ _ _ _) = _
  rw [cappedPath_trans, cappedPath_trans, cappedPath_symm]

end Topology.HomotopyFiber
