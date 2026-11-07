/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.CappedTriangleNormalization

/-!
# Marking the original capped spherical triangle

The source-return disk has a literal radial formula. For an actual spherical
triangle, its outer two boundary segments disappear, and its middle segment
is exactly the ordered stick-breaking quotient with a coordinate reversal.
An actual endpoint-fixed interval homotopy removes the middle-segment pause.
The coordinate transposition and reversal signs then cancel.
-/

/-! Implementation source: `Quillen/Topology/HomotopyFiber/SphericalCappedTriangle.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual fiber paths, source returns,
ordered face maps and signs are retained directly on native singular simplices. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open stdSimplex FundamentalGroupoid
open scoped Topology unitInterval
universe u

namespace Topology.HomotopyFiber

/-- The contributing boundary segment starts after the original quarter-time pause. -/
theorem triangleMiddleParameter_eq_zero (s : unitInterval) (hs : (s : ℝ) ≤ 1 / 4) :
    triangleMiddleParameter s = 0 :=
  Set.projIcc_of_le_left _ (by linarith)

/-- The contributing boundary segment ends at the original half time. -/
theorem triangleMiddleParameter_eq_one (s : unitInterval) (hs : 1 / 2 ≤ (s : ℝ)) :
    triangleMiddleParameter s = 1 :=
  Set.projIcc_of_right_le _ (by linarith)

/-- The exact middle-segment clock is a continuous based path of the interval. -/
def triangleMiddlePath : Path (0 : unitInterval) 1 where
  toFun := triangleMiddleParameter
  continuous_toFun := by unfold triangleMiddleParameter; fun_prop
  source' := triangleMiddleParameter_eq_zero 0 (by norm_num)
  target' := triangleMiddleParameter_eq_one 1 (by norm_num)

variable {Y : Type u} [TopologicalSpace Y] {y : Y}

/-- The original radial return of a spherical triangle has the explicit ordered cube formula. -/
theorem spherical_triangleRadialPoint (a : SphericalSimplex Y y 2) (t s : unitInterval) :
    a (triangleRadialPoint t s) =
      a.toGenLoopStick (Fin.cons t
        (fun _ : Fin 1 ↦ unitInterval.symm (triangleMiddleParameter s))) := by
  by_cases hlo : (s : ℝ) ≤ 1 / 4
  · have hleft : a (triangleRadialPoint t s) = y := by
      apply a.boundary
      refine ⟨2, ?_⟩
      rw [triangleRadialPoint_weights, standardTriangleBoundary_left_weight s hlo]
      simp [show (0 : Fin 3) ≠ 2 by decide]
    rw [hleft, triangleMiddleParameter_eq_zero s hlo]
    exact (a.toGenLoopStick.property _ ⟨1, Or.inr (by
      change unitInterval.symm (0 : unitInterval) = 1
      exact unitInterval.symm_zero)⟩).symm
  · by_cases hhi : (s : ℝ) ≤ 1 / 2
    · exact congrArg a (triangleRadialPoint_middle t s (lt_of_not_ge hlo) hhi)
    · have hright : a (triangleRadialPoint t s) = y := by
        apply a.boundary
        refine ⟨1, ?_⟩
        rw [triangleRadialPoint_weights, standardTriangleBoundary_right_weight s (lt_of_not_ge hhi)]
        norm_num
      rw [hright, triangleMiddleParameter_eq_one s (le_of_not_ge hhi)]
      exact (a.toGenLoopStick.property _ ⟨1, Or.inl (by
        change unitInterval.symm (1 : unitInterval) = 0
        exact unitInterval.symm_one)⟩).symm

/-- Swap the original two coordinates and reverse the second input coordinate. -/
def reflectedSwap (p : GenLoop (Fin 2) Y y) : GenLoop (Fin 2) Y y :=
  transposeGenLoop 0 1 (by decide) (GenLoop.symmAt 1 p)

/-- The representative retains the precise coordinate order before taking its class. -/
theorem reflectedSwap_apply (p : GenLoop (Fin 2) Y y) (z : Fin 2 → unitInterval) :
    reflectedSwap p z = p (Fin.cons (z 1) (fun _ : Fin 1 ↦ unitInterval.symm (z 0))) := by
  change p (fun j ↦ if j = 1 then
      unitInterval.symm (cubeCoordinateSwap 0 1 z 1) else cubeCoordinateSwap 0 1 z j) = _
  congr 1
  funext j
  fin_cases j <;> rfl

/-- The proved reflection and transposition signs cancel in the original Pi-two group. -/
theorem reflectedSwap_class (p : GenLoop (Fin 2) Y y) :
    (Quotient.mk' (reflectedSwap p) : HomotopyGroup.Pi 2 Y y) = Quotient.mk' p := by
  change (Quotient.mk' (transposeGenLoop 0 1 (by decide) (GenLoop.symmAt 1 p)) :
    HomotopyGroup.Pi 2 Y y) = _
  rw [transposeGenLoop_class]
  exact (congrArg (fun b : HomotopyGroup.Pi 2 Y y ↦ b⁻¹)
    (HomotopyGroup.inv_spec (i := (1 : Fin 2)) (p := p)).symm).trans (inv_inv _)

/-- Reparametrize only the first original coordinate by the exact middle-segment path. -/
def middleReparam (p : GenLoop (Fin 2) Y y) : GenLoop (Fin 2) Y y :=
  ⟨⟨fun z ↦ p (Function.update z 0 (triangleMiddlePath (z 0))), by
      apply p.val.continuous.comp
      fun_prop⟩, by
    intro z hz
    apply p.property
    obtain ⟨i, hi⟩ := hz
    fin_cases i
    · change z 0 = 0 ∨ z 0 = 1 at hi
      rcases hi with hi | hi
      · exact ⟨0, Or.inl (by
          change triangleMiddlePath (z 0) = 0
          rw [hi, triangleMiddlePath.source])⟩
      · exact ⟨0, Or.inr (by
          change triangleMiddlePath (z 0) = 1
          rw [hi, triangleMiddlePath.target])⟩
    · exact ⟨1, by simpa using hi⟩⟩

/-- The interval reparametrization is removed by an actual cube-boundary-relative homotopy. -/
def middleReparamHomotopy (p : GenLoop (Fin 2) Y y) :
    p.val.HomotopyRel (middleReparam p).val (Cube.boundary (Fin 2)) := by
  let H := Path.Homotopy.reparam Path.id triangleMiddlePath triangleMiddlePath.continuous
    triangleMiddlePath.source triangleMiddlePath.target
  exact {
    toFun := fun z ↦ p (Function.update z.2 0 (H (z.1, z.2 0)))
    continuous_toFun := p.val.continuous.comp (by fun_prop)
    map_zero_left := fun z ↦ by
      rw [H.apply_zero]
      change p (Function.update z 0 (z 0)) = p z
      rw [Function.update_eq_self]
    map_one_left := fun z ↦ by rw [H.apply_one]; rfl
    prop' := fun t z hz ↦ by
      rw [p.property z hz]
      apply p.property
      obtain ⟨i, hi⟩ := hz
      fin_cases i
      · change z 0 = 0 ∨ z 0 = 1 at hi
        rcases hi with hi | hi
        · exact ⟨0, Or.inl (by change H (t, z 0) = 0; rw [hi, H.source])⟩
        · exact ⟨0, Or.inr (by change H (t, z 0) = 1; rw [hi, H.target])⟩
      · exact ⟨1, by simpa using hi⟩ }

/-- The marked radial-return cube of the original spherical triangle. -/
def sphericalRadialCube (a : SphericalSimplex Y y 2) : GenLoop (Fin 2) Y y :=
  middleReparam (reflectedSwap a.toGenLoopStick)

/-- Every point of this cube is the actual source-return disk value. -/
theorem sphericalRadialCube_apply (a : SphericalSimplex Y y 2) (z : Fin 2 → unitInterval) :
    sphericalRadialCube a z = a (triangleRadialPoint (z 1) (z 0)) := by
  rw [spherical_triangleRadialPoint]
  change reflectedSwap a.toGenLoopStick (Function.update z 0 (triangleMiddlePath (z 0))) = _
  rw [reflectedSwap_apply]
  rfl

/-- The original radial-return cube represents exactly the original stick-breaking Pi-two class. -/
theorem sphericalRadialCube_class (a : SphericalSimplex Y y 2) :
    (Quotient.mk' (sphericalRadialCube a) : HomotopyGroup.Pi 2 Y y) =
      a.homotopyClassStick := by
  have he : (Quotient.mk' (sphericalRadialCube a) : HomotopyGroup.Pi 2 Y y) =
      Quotient.mk' (reflectedSwap a.toGenLoopStick) :=
    Quotient.sound ⟨(middleReparamHomotopy (reflectedSwap a.toGenLoopStick)).symm⟩
  exact he.trans (reflectedSwap_class a.toGenLoopStick)

/-- Every original vertex of the actual spherical triangle is its given basepoint. -/
theorem sphericalTriangle_vertex (a : SphericalSimplex Y y 2) (i : Fin 3) :
    a.val (stdSimplex.vertex i) = y := by
  apply a.boundary
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, i ≠ j := by fin_cases i <;> decide
  exact ⟨j, by simp [stdSimplex.vertex, hj]⟩

/-- Every actual edge is literally the constant path, with no change of parametrization. -/
theorem sphericalTriangle_edge (a : SphericalSimplex Y y 2) (i j : Fin 3) :
    sourceTriangleEdge a.val (sphericalTriangle_vertex a) i j = Path.refl y := by
  ext s
  change a (LocalCoefficients.simplexEdgePoint i j s) = y
  apply a.boundary
  obtain ⟨k, hik, hjk⟩ : ∃ k : Fin 3, i ≠ k ∧ j ≠ k := by
    fin_cases i <;> fin_cases j <;> decide
  refine ⟨k, ?_⟩
  rw [simplexEdgePoint_weights]
  simp only [ite_eq_right hik, ite_eq_right hjk, add_zero]

/-- The cap of a spherical edge is the actual constant loop-space path. -/
def sphericalTriangleCap (a : SphericalSimplex Y y 2) (i j : Fin 3) :
    Path (basedLoopMap (ContinuousMap.id Y) (rfl : y = y)
      (sourceTriangleEdge a.val (sphericalTriangle_vertex a) i j)) (Path.refl y) :=
  (Path.refl (Path.refl y)).cast
    ((congrArg (basedLoopMap (ContinuousMap.id Y) (rfl : y = y))
      (sphericalTriangle_edge a i j)).trans (basedLoopMap_refl _ _)) rfl

/-- The original full source boundary is constant for a spherical triangle. -/
theorem sphericalTriangle_boundary (a : SphericalSimplex Y y 2) :
    sourceTriangleBoundary a.val (sphericalTriangle_vertex a) = Path.refl y := by
  unfold sourceTriangleBoundary
  rw [sphericalTriangle_edge, sphericalTriangle_edge, sphericalTriangle_edge,
    Path.refl_trans_refl]
  exact Path.refl_trans_refl

/-- The original radial-return path as a based loop in the actual target loop space. -/
def sphericalTriangleReturnLoop (a : SphericalSimplex Y y 2) :
    Path (Path.refl y) (Path.refl y) :=
  (sourceTriangleReturn a.val (sphericalTriangle_vertex a)).cast
    (sphericalTriangle_boundary a).symm rfl

/-- Both coordinates of the source return are retained literally. -/
theorem sphericalTriangleReturnLoop_apply (a : SphericalSimplex Y y 2)
    (t s : unitInterval) : sphericalTriangleReturnLoop a t s = a (triangleRadialPoint t s) := rfl

/-- Uncurrying the original loop-space class gives the marked radial cube. -/
theorem sphericalTriangleReturnLoop_class (a : SphericalSimplex Y y 2) :
    (loopShiftMulEquiv (x := y) 0).symm
      (HomotopyGroup.pi1MulEquivFundamentalGroup.symm
        (⟦sphericalTriangleReturnLoop a⟧ : FundamentalGroup _ (Path.refl y))) =
      a.homotopyClassStick := by
  have he : (loopShiftMulEquiv (x := y) 0).symm
      (HomotopyGroup.pi1MulEquivFundamentalGroup.symm
        (⟦sphericalTriangleReturnLoop a⟧ : FundamentalGroup _ (Path.refl y))) =
      (Quotient.mk' (sphericalRadialCube a) : HomotopyGroup.Pi 2 Y y) := by
    apply congrArg Quotient.mk'
    ext z
    exact (sphericalRadialCube_apply a z).symm
  exact he.trans (sphericalRadialCube_class a)

/-- For a constant source loop and constant cap, the two return inversions cancel. -/
theorem cappedLoopSphereClass_constant_cap
    (R : Path (Path.refl y) (Path.refl y)) :
    cappedLoopSphereClass (ContinuousMap.id Y) (rfl : y = y)
      (Path.refl y) (Path.refl (Path.refl y)) R =
    (loopShiftMulEquiv (x := y) 0).symm
      (HomotopyGroup.pi1MulEquivFundamentalGroup.symm
        (⟦R⟧ : FundamentalGroup _ (Path.refl y))) := by
  have hβ : cappedLoopReturn (ContinuousMap.id Y) (rfl : y = y)
      (Path.refl y) (Path.refl (Path.refl y)) R = R.symm.trans (Path.refl (Path.refl y)) := by
    ext s t
    rfl
  have he : (⟦cappedLoopReturn (ContinuousMap.id Y) (rfl : y = y)
      (Path.refl y) (Path.refl (Path.refl y)) R⟧ : FundamentalGroup _ (Path.refl y)) =
      (⟦R.symm⟧ : FundamentalGroup _ (Path.refl y)) := by
    rw [hβ]
    exact Quotient.sound (Path.Homotopic.trans_refl R.symm)
  have hi : HomotopyGroup.pi1MulEquivFundamentalGroup.symm
      (⟦R.symm⟧ : FundamentalGroup _ (Path.refl y)) =
      (HomotopyGroup.pi1MulEquivFundamentalGroup.symm
        (⟦R⟧ : FundamentalGroup _ (Path.refl y)))⁻¹ :=
    @MulEquiv.map_inv (FundamentalGroup (Path y y) (Path.refl y))
      (HomotopyGroup.Pi 1 (Path y y) (Path.refl y)) inferInstance inferInstance
      (HomotopyGroup.pi1MulEquivFundamentalGroup (X := Path y y) (x := Path.refl y)).symm
      (Path.Homotopic.Quotient.mk R)
  unfold cappedLoopSphereClass
  rw [he, hi, map_inv, inv_inv]

/-- The frozen cap-sphere value marks exactly the original spherical Pi-two representative. -/
theorem cappedTriangleSphereClass_spherical (a : SphericalSimplex Y y 2) :
    cappedTriangleSphereClass (ContinuousMap.id Y) (rfl : y = y) a.val
      (sphericalTriangle_vertex a) (sphericalTriangleCap a 0 1)
      (sphericalTriangleCap a 1 2) (sphericalTriangleCap a 0 2) = a.homotopyClassStick := by
  have hc : cappedTriangleNull (ContinuousMap.id Y) (rfl : y = y) a.val
      (sphericalTriangle_vertex a) (sphericalTriangleCap a 0 1)
      (sphericalTriangleCap a 1 2) (sphericalTriangleCap a 0 2) =
        (Path.refl (Path.refl y)).cast
          (congrArg (basedLoopMap (ContinuousMap.id Y) (rfl : y = y))
            (sphericalTriangle_boundary a)) rfl := by
    ext s t
    change (((Path.refl y).trans (Path.refl y)).trans (Path.refl y).symm) t = y
    rw [Path.refl_trans_refl]
    exact congrArg (fun p : Path y y ↦ p t) Path.refl_trans_refl
  have he : cappedTriangleSphereClass (ContinuousMap.id Y) (rfl : y = y) a.val
      (sphericalTriangle_vertex a) (sphericalTriangleCap a 0 1)
      (sphericalTriangleCap a 1 2) (sphericalTriangleCap a 0 2) =
      cappedLoopSphereClass (ContinuousMap.id Y) (rfl : y = y) (Path.refl y)
        (Path.refl (Path.refl y)) (sphericalTriangleReturnLoop a) := by
    unfold cappedTriangleSphereClass
    rw [hc]
    rfl
  exact he.trans ((cappedLoopSphereClass_constant_cap (sphericalTriangleReturnLoop a)).trans
    (sphericalTriangleReturnLoop_class a))

end Topology.HomotopyFiber
