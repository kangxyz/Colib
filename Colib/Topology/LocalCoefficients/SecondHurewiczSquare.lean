/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.LocalCoefficients.TrianglePrismComparison
public import Colib.Topology.LocalCoefficients.PeriodicSquare
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The original second Hurewicz class of a square

The original chains, signs, maps, basepoints and stated hypotheses are retained.
-/
/-! Implementation source: `Quillen/Topology/LocalCoefficients/SecondHurewiczSquare.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Native simplex coordinates,
original maps, endpoint paths, coefficient universe and chain signs are retained.
The spherical representatives use the explicit ordered stick-breaking quotient.
-/
@[expose] public section

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Limits Topology
open scoped Simplicial Topology unitInterval

namespace FundamentalGroupoid.LocalCoefficients.SecondHurewiczSquare
open SecondHurewicz SingularBar
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Whole periodic homotopies preserve the original oriented square class. -/
theorem squareTwoCycle_homotopy
    {sq qt : C(I × I, Y)} (H : sq.Homotopy qt)
    (hsq₁ : ∀ t, sq (0, t) = sq (1, t)) (hsq₂ : ∀ t, sq (t, 0) = sq (t, 1))
    (hqt₁ : ∀ t, qt (0, t) = qt (1, t)) (hqt₂ : ∀ t, qt (t, 0) = qt (t, 1))
    (hH₁ : ∀ s t, H (s, (0, t)) = H (s, (1, t)))
    (hH₂ : ∀ s t, H (s, (t, 0)) = H (s, (t, 1))) :
    (Chains Y).homologyπ 2 (squareTwoCycle sq hsq₁ hsq₂) =
      (Chains Y).homologyπ 2 (squareTwoCycle qt hqt₁ hqt₂) := by
  have he := TrianglePrismComparison.paired_chain_boundary
    (H.compContinuousMap lowerPoint)
    (H.compContinuousMap (ContinuousMap.prodSwap.comp lowerPoint))
    (fun s x ↦ ContinuousMap.congr_fun (periodic_lowerFace_zero (H.curry s) (hH₁ s)) x)
    (fun s x ↦ ContinuousMap.congr_fun (periodic_lowerFace_one (H.curry s)) x)
    (fun s x ↦ ContinuousMap.congr_fun (periodic_lowerFace_two (H.curry s) (hH₂ s)) x)
  symm
  refine homology_eq_of_boundary _ _
    (TrianglePrismComparison.chain (H.compContinuousMap lowerPoint) -
      TrianglePrismComparison.chain
        (H.compContinuousMap (ContinuousMap.prodSwap.comp lowerPoint))) ?_
  rw [iCycles_squareTwoCycle, iCycles_squareTwoCycle]
  exact he

/-- The original chain map takes each actual simplex generator to its image simplex. -/
theorem pushforward_simplexChain (f : C(X, Y)) {n : ℕ} (a : SingularSimplex X ⦋n⦌) :
    (pushforwardChainMap f (constant Y integralCoefficients.{u})).f n (simplexChain a) =
      simplexChain (f.comp a) :=
  ConcreteCategory.congr_hom
    (chainInclusion_pushforwardModuleMap f (constant Y integralCoefficients.{u}) a)
      (ULift.up 1)

/-- The literal lower-minus-upper chain is natural for the original continuous map. -/
theorem squareTwoChain_map (f : C(X, Y)) (sq : C(I × I, X)) :
    (pushforwardChainMap f (constant Y integralCoefficients.{u})).f 2 (squareTwoChain sq) =
      squareTwoChain (f.comp sq) := by
  change (pushforwardChainMap f (constant Y integralCoefficients.{u})).f 2
    (simplexChain (lowerTriangle sq) - simplexChain (upperTriangle sq)) = _
  rw [map_sub, pushforward_simplexChain, pushforward_simplexChain]
  rfl

/-- The same actual map on original categorical square cycles. -/
theorem squareTwoCycle_map (f : C(X, Y)) (sq : C(I × I, X))
    (h₁ : ∀ t, sq (0, t) = sq (1, t)) (h₂ : ∀ t, sq (t, 0) = sq (t, 1)) :
    HomologicalComplex.cyclesMap
      (pushforwardChainMap f (constant Y integralCoefficients.{u})) 2
        (squareTwoCycle sq h₁ h₂) =
      squareTwoCycle (f.comp sq) (fun t ↦ congrArg f (h₁ t))
        (fun t ↦ congrArg f (h₂ t)) := by
  apply (ModuleCat.mono_iff_injective ((Chains Y).iCycles 2)).mp inferInstance
  have hn := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i
      (pushforwardChainMap f (constant Y integralCoefficients.{u})) 2)
        (squareTwoCycle sq h₁ h₂)
  change (Chains Y).iCycles 2 (HomologicalComplex.cyclesMap
      (pushforwardChainMap f (constant Y integralCoefficients.{u})) 2
        (squareTwoCycle sq h₁ h₂)) =
    (pushforwardChainMap f (constant Y integralCoefficients.{u})).f 2
      ((Chains X).iCycles 2 (squareTwoCycle sq h₁ h₂)) at hn
  rw [hn, iCycles_squareTwoCycle, iCycles_squareTwoCycle]
  exact squareTwoChain_map f sq

/-- The original homology arrow preserves the specified square representative. -/
theorem squareClass_map (f : C(X, Y)) (sq : C(I × I, X))
    (h₁ : ∀ t, sq (0, t) = sq (1, t)) (h₂ : ∀ t, sq (t, 0) = sq (t, 1)) :
    pushforwardHomologyMap f (constant Y integralCoefficients.{u}) 2
      ((Chains X).homologyπ 2 (squareTwoCycle sq h₁ h₂)) =
    (Chains Y).homologyπ 2 (squareTwoCycle (f.comp sq)
      (fun t ↦ congrArg f (h₁ t)) (fun t ↦ congrArg f (h₂ t))) := by
  have hn := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality
      (pushforwardChainMap f (constant Y integralCoefficients.{u})) 2)
        (squareTwoCycle sq h₁ h₂)
  exact hn.trans (congrArg ((Chains Y).homologyπ 2) (squareTwoCycle_map f sq h₁ h₂))

/-- The actual affine map specified by a function on the displayed vertices. -/
def vertexMap {m n : ℕ} (v : Fin (m + 1) → Fin (n + 1)) :
    C(_root_.stdSimplex ℝ (Fin (m + 1)), _root_.stdSimplex ℝ (Fin (n + 1))) :=
  ⟨stdSimplex.map v, stdSimplex.continuous_map v⟩

/-- A missing target vertex forces the full affine image into the actual simplex boundary. -/
theorem vertexMap_mem_boundary {m n : ℕ} (v : Fin (m + 1) → Fin (n + 1))
    (i : Fin (n + 1)) (hi : ∀ j, v j ≠ i) (x : _root_.stdSimplex ℝ (Fin (m + 1))) :
    vertexMap v x ∈ stdSimplex.boundary n := by
  refine ⟨i, ?_⟩
  exact stdSimplex.map_apply_eq_zero_of_not_mem_range v x i
    (by rintro ⟨j, hj⟩; exact hi j hj)

/-- A spherical simplex is literally constant after an affine map missing a vertex. -/
theorem spherical_vertexMap_const {y : Y} (a : SphericalSimplex Y y 2)
    {m : ℕ} (v : Fin (m + 1) → Fin 3) (i : Fin 3) (hi : ∀ j, v j ≠ i) :
    a.val.comp (vertexMap v) = ContinuousMap.const _ y := by
  ext x
  exact a.boundary _ (vertexMap_mem_boundary v i hi x)

/-- Face restriction retains the actual vertex function without orientation changes. -/
theorem restrict_vertexMap {y : Y} (a : SphericalSimplex Y y 2)
    (v : Fin 4 → Fin 3) (j : Fin 4) (w : Fin 3 → Fin 3)
    (hw : ∀ i, v (j.succAbove i) = w i) :
    restrictSimplex (a.val.comp (vertexMap v)) (SimplexCategory.δ j) =
      a.val.comp (vertexMap w) := by
  ext x
  change a (stdSimplex.map v (stdSimplex.map (SimplexCategory.δ j) x)) =
    a (stdSimplex.map w x)
  rw [stdSimplex.map_comp_apply]
  apply congrArg a
  congr 1
  funext i
  exact hw i

/-- The literal reversal of the three simplex vertices. -/
def reversedTriangle {y : Y} (a : SphericalSimplex Y y 2) : SingularSimplex Y ⦋2⦌ :=
  a.val.comp (vertexMap ![2, 1, 0])

/-- Two explicit tetrahedra compare vertex reversal with the negative spherical cycle. -/
def reversalChain {y : Y} (a : SphericalSimplex Y y 2) : (Chains Y).X 3 :=
  simplexChain (a.val.comp (vertexMap ![0, 2, 1, 0])) -
    simplexChain (a.val.comp (vertexMap ![0, 1, 2, 1]))

/-- The original differential fixes the reversal sign, retaining both constant triangles. -/
theorem reversalChain_boundary {y : Y} (a : SphericalSimplex Y y 2) :
    (Chains Y).d 3 2 (reversalChain a) =
      simplexChain (reversedTriangle a) + simplexChain a.val -
        (simplexChain (ContinuousMap.const _ y) + simplexChain (ContinuousMap.const _ y)) := by
  have h00 := restrict_vertexMap a ![0, 2, 1, 0] 0 ![2, 1, 0]
    (by intro i; fin_cases i <;> rfl)
  have h01 := restrict_vertexMap a ![0, 2, 1, 0] 1 ![0, 1, 0]
    (by intro i; fin_cases i <;> rfl)
  have h02 := restrict_vertexMap a ![0, 2, 1, 0] 2 ![0, 2, 0]
    (by intro i; fin_cases i <;> rfl)
  have h03 := restrict_vertexMap a ![0, 2, 1, 0] 3 ![0, 2, 1]
    (by intro i; fin_cases i <;> rfl)
  have h10 := restrict_vertexMap a ![0, 1, 2, 1] 0 ![1, 2, 1]
    (by intro i; fin_cases i <;> rfl)
  have h11 := restrict_vertexMap a ![0, 1, 2, 1] 1 ![0, 2, 1]
    (by intro i; fin_cases i <;> rfl)
  have h12 := restrict_vertexMap a ![0, 1, 2, 1] 2 ![0, 1, 1]
    (by intro i; fin_cases i <;> rfl)
  have h13 := restrict_vertexMap a ![0, 1, 2, 1] 3 ![0, 1, 2]
    (by intro i; fin_cases i <;> rfl)
  have hc01 := spherical_vertexMap_const a ![0, 1, 0] 2
    (by intro i; fin_cases i <;> decide)
  have hc02 := spherical_vertexMap_const a ![0, 2, 0] 1
    (by intro i; fin_cases i <;> decide)
  have hc10 := spherical_vertexMap_const a ![1, 2, 1] 0
    (by intro i; fin_cases i <;> decide)
  have hc12 := spherical_vertexMap_const a ![0, 1, 1] 2
    (by intro i; fin_cases i <;> decide)
  have hid : a.val.comp (vertexMap ![0, 1, 2]) = a.val := by
    have he : (![0, 1, 2] : Fin 3 → Fin 3) = id := by
      funext i; fin_cases i <;> rfl
    ext x
    change a (stdSimplex.map ![0, 1, 2] x) = a x
    rw [he, stdSimplex.map_id_apply]
  rw [reversalChain, map_sub, tetrahedron_boundary, tetrahedron_boundary,
    h00, h01, h02, h03, h10, h11, h12, h13, hc01, hc02, hc10, hc12, hid]
  change _ = simplexChain (a.val.comp (vertexMap ![2, 1, 0])) + _ - _
  abel

/-- The displayed square coordinates in the original cubical domain. -/
def cubeCoordinates : C(I × I, Fin 2 → I) :=
  ⟨fun z ↦ ![z.1, z.2], by fun_prop⟩

/-- The actual square underlying an original based two-cube, in its original coordinate order. -/
def cubeSquare {y : Y} (b : GenLoop (Fin 2) Y y) : C(I × I, Y) :=
  b.val.comp cubeCoordinates

/-- The specified stick-breaking simplex point, read on the ordinary square. -/
def stickSquare : C(I × I, _root_.stdSimplex ℝ (Fin 3)) :=
  (Cube.stickBreakingMap 2).comp cubeCoordinates

/-- Joint convex interpolation in the actual barycentric simplex. -/
def blend (f g : C(_root_.stdSimplex ℝ (Fin 3), _root_.stdSimplex ℝ (Fin 3))) : f.Homotopy g where
  toFun z := ⟨fun i ↦ (1 - (z.1 : ℝ)) * f z.2 i + (z.1 : ℝ) * g z.2 i,
    (by
      intro i
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr z.1.property.2)
        (stdSimplex.zero_le (f z.2) i))
        (mul_nonneg z.1.property.1 (stdSimplex.zero_le (g z.2) i))),
    (by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        stdSimplex.sum_eq_one, stdSimplex.sum_eq_one]
      ring)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      ((continuous_apply i).comp
        (continuous_subtype_val.comp (f.continuous.comp continuous_snd)))).add
      ((continuous_subtype_val.comp continuous_fst).mul
        ((continuous_apply i).comp
          (continuous_subtype_val.comp (g.continuous.comp continuous_snd))))
  map_zero_left x := by
    ext i
    change (1 - (0 : ℝ)) * f x i + 0 * g x i = f x i
    ring
  map_one_left x := by
    ext i
    change (1 - (1 : ℝ)) * f x i + 1 * g x i = g x i
    ring

/-- Convex interpolation retains a common zero barycentric coordinate. -/
theorem blend_mem_boundary (f g : C(_root_.stdSimplex ℝ (Fin 3), _root_.stdSimplex ℝ (Fin 3)))
    (s : I) (x : _root_.stdSimplex ℝ (Fin 3)) (i : Fin 3)
    (hf : f x i = 0) (hg : g x i = 0) :
    blend f g (s, x) ∈ stdSimplex.boundary 2 := by
  refine ⟨i, ?_⟩
  change (1 - (s : ℝ)) * f x i + (s : ℝ) * g x i = 0
  rw [hf, hg, mul_zero, mul_zero, add_zero]

/-- The affine image of an edge omits every vertex absent from its two endpoints. -/
theorem vertexMap_edge_zero (v : Fin 3 → Fin 3) (i j k : Fin 3)
    (hi : v i ≠ k) (hj : v j ≠ k) (t : I) :
    vertexMap v (simplexEdgePoint i j t) k = 0 := by
  change stdSimplex.map v (stdSimplex.map
    (fun e : Fin 2 ↦ if e = 0 then i else j) (stdSimplexHomeomorphUnitInterval.symm t)) k = 0
  rw [stdSimplex.map_comp_apply]
  apply stdSimplex.map_apply_eq_zero_of_not_mem_range
  rintro ⟨e, he⟩
  fin_cases e
  · exact hi he
  · exact hj he

/-- The original lower half is straightened to the vertex sequence 2,0,0. -/
def lowerBlend {y : Y} (a : SphericalSimplex Y y 2) :
    (lowerTriangle (cubeSquare a.toGenLoopStick)).Homotopy
      (a.val.comp (vertexMap ![2, 0, 0])) :=
  (ContinuousMap.Homotopy.refl a.val).comp
    (blend (lowerTriangle stickSquare) (vertexMap ![2, 0, 0]))

/-- The original upper half is straightened to the vertex sequence 2,1,0. -/
def upperBlend {y : Y} (a : SphericalSimplex Y y 2) :
    (upperTriangle (cubeSquare a.toGenLoopStick)).Homotopy (reversedTriangle a) :=
  (ContinuousMap.Homotopy.refl a.val).comp
    (blend (upperTriangle stickSquare) (vertexMap ![2, 1, 0]))

/-- The lower straightening stays based on both exterior edges. -/
theorem lowerBlend_exterior {y : Y} (a : SphericalSimplex Y y 2) (s t : I) :
    lowerBlend a (s, simplexEdgePoint 1 2 t) = y ∧
      lowerBlend a (s, simplexEdgePoint 0 1 t) = y := by
  constructor
  · apply a.boundary
    apply blend_mem_boundary _ _ _ _ 1
    · rw [lowerTriangle_edge12]
      change (1 - (1 : ℝ)) * (t : ℝ) = 0
      ring
    · exact vertexMap_edge_zero _ _ _ _ (by decide) (by decide) t
  · apply a.boundary
    apply blend_mem_boundary _ _ _ _ 1
    · rw [lowerTriangle_edge01]
      change (1 - (t : ℝ)) * 0 = 0
      ring
    · exact vertexMap_edge_zero _ _ _ _ (by decide) (by decide) t

/-- The upper straightening stays based on both exterior edges. -/
theorem upperBlend_exterior {y : Y} (a : SphericalSimplex Y y 2) (s t : I) :
    upperBlend a (s, simplexEdgePoint 0 1 t) = y ∧
      upperBlend a (s, simplexEdgePoint 1 2 t) = y := by
  constructor
  · apply a.boundary
    apply blend_mem_boundary _ _ _ _ 0
    · rw [upperTriangle_edge01]
      rfl
    · exact vertexMap_edge_zero _ _ _ _ (by decide) (by decide) t
  · apply a.boundary
    apply blend_mem_boundary _ _ _ _ 2
    · rw [upperTriangle_edge12]
      change (1 - (t : ℝ)) * ((1 - (1 : ℝ)) * 1) = 0
      ring
    · exact vertexMap_edge_zero _ _ _ _ (by decide) (by decide) t

/-- Both simplex straightenings agree along their entire common diagonal. -/
theorem blend_diagonal {y : Y} (a : SphericalSimplex Y y 2) (s t : I) :
    lowerBlend a (s, simplexEdgePoint 0 2 t) =
      upperBlend a (s, simplexEdgePoint 0 2 t) := by
  have h₀ : lowerTriangle stickSquare (simplexEdgePoint 0 2 t) =
      upperTriangle stickSquare (simplexEdgePoint 0 2 t) := by
    rw [lowerTriangle_edge02, upperTriangle_edge02]
  have h₁ : vertexMap (n := 2) ![2, 0, 0] (simplexEdgePoint 0 2 t) =
      vertexMap ![2, 1, 0] (simplexEdgePoint 0 2 t) := by
    change stdSimplex.map ![2, 0, 0]
        (stdSimplex.map (fun e : Fin 2 ↦ if e = 0 then (0 : Fin 3) else 2)
          (stdSimplexHomeomorphUnitInterval.symm t)) =
      stdSimplex.map ![2, 1, 0]
        (stdSimplex.map (fun e : Fin 2 ↦ if e = 0 then (0 : Fin 3) else 2)
          (stdSimplexHomeomorphUnitInterval.symm t))
    rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply]
    congr 1
    funext e
    fin_cases e <;> rfl
  apply congrArg a
  ext i
  change (1 - (s : ℝ)) * lowerTriangle stickSquare (simplexEdgePoint 0 2 t) i +
      (s : ℝ) * vertexMap ![2, 0, 0] (simplexEdgePoint 0 2 t) i =
    (1 - (s : ℝ)) * upperTriangle stickSquare (simplexEdgePoint 0 2 t) i +
      (s : ℝ) * vertexMap ![2, 1, 0] (simplexEdgePoint 0 2 t) i
  rw [h₀, h₁]

/-- The actual paired prism chain for straightening both halves of the stick square. -/
def blendChain {y : Y} (a : SphericalSimplex Y y 2) : (Chains Y).X 3 :=
  TrianglePrismComparison.chain (lowerBlend a) - TrianglePrismComparison.chain (upperBlend a)

/-- The straightening boundary retains the exact lower-minus-upper square chain. -/
theorem blendChain_boundary {y : Y} (a : SphericalSimplex Y y 2) :
    (Chains Y).d 3 2 (blendChain a) =
      (simplexChain (ContinuousMap.const _ y) - simplexChain (reversedTriangle a)) -
        squareTwoChain (cubeSquare a.toGenLoopStick) := by
  have he := TrianglePrismComparison.paired_chain_boundary (lowerBlend a) (upperBlend a)
    (by
      intro s x
      obtain ⟨t, rfl⟩ := stdSimplexHomeomorphUnitInterval.symm.surjective x
      change restrictSimplex ((lowerBlend a).curry s) (SimplexCategory.δ 0)
          (stdSimplexHomeomorphUnitInterval.symm t) =
        restrictSimplex ((upperBlend a).curry s) (SimplexCategory.δ 2)
          (stdSimplexHomeomorphUnitInterval.symm t)
      rw [restrictTriangle_interval, restrictTriangle_interval]
      exact (lowerBlend_exterior a s t).1.trans (upperBlend_exterior a s t).1.symm)
    (by
      intro s x
      obtain ⟨t, rfl⟩ := stdSimplexHomeomorphUnitInterval.symm.surjective x
      change restrictSimplex ((lowerBlend a).curry s) (SimplexCategory.δ 1)
          (stdSimplexHomeomorphUnitInterval.symm t) =
        restrictSimplex ((upperBlend a).curry s) (SimplexCategory.δ 1)
          (stdSimplexHomeomorphUnitInterval.symm t)
      rw [restrictTriangle_interval, restrictTriangle_interval]
      exact blend_diagonal a s t)
    (by
      intro s x
      obtain ⟨t, rfl⟩ := stdSimplexHomeomorphUnitInterval.symm.surjective x
      change restrictSimplex ((lowerBlend a).curry s) (SimplexCategory.δ 2)
          (stdSimplexHomeomorphUnitInterval.symm t) =
        restrictSimplex ((upperBlend a).curry s) (SimplexCategory.δ 0)
          (stdSimplexHomeomorphUnitInterval.symm t)
      rw [restrictTriangle_interval, restrictTriangle_interval]
      exact (lowerBlend_exterior a s t).2.trans (upperBlend_exterior a s t).2.symm)
  have hc := spherical_vertexMap_const a ![2, 0, 0] 1
    (by intro i; fin_cases i <;> decide)
  exact he.trans (by rw [hc]; rfl)

/-- An original based cube is periodic in the first displayed coordinate. -/
theorem cubeSquare_first {y : Y} (b : GenLoop (Fin 2) Y y) (t : I) :
    cubeSquare b (0, t) = cubeSquare b (1, t) :=
  (b.property ![0, t] ⟨0, Or.inl rfl⟩).trans
    (b.property ![1, t] ⟨0, Or.inr rfl⟩).symm

/-- An original based cube is periodic in the second displayed coordinate. -/
theorem cubeSquare_second {y : Y} (b : GenLoop (Fin 2) Y y) (t : I) :
    cubeSquare b (t, 0) = cubeSquare b (t, 1) :=
  (b.property ![t, 0] ⟨1, Or.inl rfl⟩).trans
    (b.property ![t, 1] ⟨1, Or.inr rfl⟩).symm

/-- The actual two-triangle stick square has the positive original spherical class. -/
theorem squareTwoCycle_stick {y : Y} (a : SphericalSimplex Y y 2) :
    (Chains Y).homologyπ 2 (squareTwoCycle (cubeSquare a.toGenLoopStick)
      (cubeSquare_first a.toGenLoopStick) (cubeSquare_second a.toGenLoopStick)) =
      (Chains Y).homologyπ 2 (sphericalTwoCycle a) := by
  symm
  refine homology_eq_of_boundary _ _ (blendChain a + reversalChain a) ?_
  rw [map_add, blendChain_boundary, reversalChain_boundary,
    iCycles_sphericalTwoCycle, iCycles_squareTwoCycle]
  change _ = (simplexChain a.val - simplexChain (ContinuousMap.const _ y)) -
    squareTwoChain (cubeSquare a.toGenLoopStick)
  abel

/-- Every original based square represents exactly its marked second Hurewicz class. -/
theorem squareTwoCycle_cube {y : Y} (b : GenLoop (Fin 2) Y y) :
    (Chains Y).homologyπ 2 (squareTwoCycle (cubeSquare b)
      (cubeSquare_first b) (cubeSquare_second b)) =
      Multiplicative.toAdd (SecondHurewicz.hom y (Quotient.mk' b)) := by
  have he := squareTwoCycle_stick (SphericalSimplex.ofGenLoopStick b)
  rw [SphericalSimplex.toGenLoopStick_ofGenLoopStick] at he
  rw [SecondHurewicz.hom_genLoop]
  exact he

/-- A whole periodic homotopy to the original based cube gives the original Hurewicz image. -/
theorem pushforward_squareTwoCycle_eq_hurewicz
    (f : C(X, Y)) (sq : C(I × I, X)) {y : Y} (b : GenLoop (Fin 2) Y y)
    (hsq₁ : ∀ t, sq (0, t) = sq (1, t)) (hsq₂ : ∀ t, sq (t, 0) = sq (t, 1))
    (H : (f.comp sq).Homotopy (cubeSquare b))
    (hH₁ : ∀ s t, H (s, (0, t)) = H (s, (1, t)))
    (hH₂ : ∀ s t, H (s, (t, 0)) = H (s, (t, 1))) :
    pushforwardHomologyMap f (constant Y integralCoefficients.{u}) 2
      ((Chains X).homologyπ 2 (squareTwoCycle sq hsq₁ hsq₂)) =
      Multiplicative.toAdd (SecondHurewicz.hom y (Quotient.mk' b)) := by
  rw [squareClass_map]
  exact (squareTwoCycle_homotopy H _ _ (cubeSquare_first b) (cubeSquare_second b)
    hH₁ hH₂).trans (squareTwoCycle_cube b)

/-- The same image retains any specified original basepoint-path correction of the cube. -/
theorem pushforward_squareTwoCycle_eq_hurewicz_transport
    (f : C(X, Y)) (sq : C(I × I, X)) {y z : Y} (b : GenLoop (Fin 2) Y y)
    (hsq₁ : ∀ t, sq (0, t) = sq (1, t)) (hsq₂ : ∀ t, sq (t, 0) = sq (t, 1))
    (H : (f.comp sq).Homotopy (cubeSquare b))
    (hH₁ : ∀ s t, H (s, (0, t)) = H (s, (1, t)))
    (hH₂ : ∀ s t, H (s, (t, 0)) = H (s, (t, 1))) (p : Path y z) :
    pushforwardHomologyMap f (constant Y integralCoefficients.{u}) 2
      ((Chains X).homologyπ 2 (squareTwoCycle sq hsq₁ hsq₂)) =
      Multiplicative.toAdd (SecondHurewicz.hom z
        (pathTransportMulEquiv p 1 (Quotient.mk' b))) := by
  rw [SecondHurewicz.hom_pathTransport]
  exact pushforward_squareTwoCycle_eq_hurewicz f sq b hsq₁ hsq₂ H hH₁ hH₂

end FundamentalGroupoid.LocalCoefficients.SecondHurewiczSquare

end
