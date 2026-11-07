/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.LocalCoefficients.Homology
public import Colib.Topology.LocalCoefficients.IntegralChainEvaluation
public import Mathlib.Topology.Homotopy.HomotopyGroup
public import Colib.Topology.LocalCoefficients.Prism
public import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory

/-!
# The original oriented singular cycle of a periodic square

Adapted from `Quillen/Topology/LocalCoefficients/PeriodicSquare.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original chains, signs,
maps, basepoints and stated hypotheses are retained, using Mathlib's actual
standard simplex and native second group homology.
-/
@[expose] public section

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Limits
open scoped Simplicial
namespace FundamentalGroupoid.LocalCoefficients.SingularBar
variable {P : Type u} [TopologicalSpace P]

private theorem nativeSimplex_map_const {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (k : κ) (x : _root_.stdSimplex ℝ ι) :
    stdSimplex.map (fun _ ↦ k) x = stdSimplex.vertex k := by
  have h : stdSimplex.map (fun _ : ι ↦ (0 : Fin 1)) x = stdSimplex.vertex 0 :=
    Subsingleton.elim _ _
  simpa only [stdSimplex.map_comp_apply, Function.comp_def, stdSimplex.map_vertex] using
    congrArg (stdSimplex.map (fun _ : Fin 1 ↦ k)) h

/-- The first square coordinate of the lower, positively oriented triangle. -/
def lowerFirst (i : Fin 3) : Fin 2 := if i = 0 then 0 else 1

/-- The second square coordinate of the lower, positively oriented triangle. -/
def lowerSecond (i : Fin 3) : Fin 2 := if i = 2 then 1 else 0

/-- The actual affine lower half of the unit square, with vertex order 00, 10, 11. -/
def lowerPoint : C(_root_.stdSimplex ℝ (Fin 3), unitInterval × unitInterval) where
  toFun z := (stdSimplexHomeomorphUnitInterval (stdSimplex.map lowerFirst z),
    stdSimplexHomeomorphUnitInterval (stdSimplex.map lowerSecond z))
  continuous_toFun :=
    (stdSimplexHomeomorphUnitInterval.continuous.comp (stdSimplex.continuous_map _)).prodMk
      (stdSimplexHomeomorphUnitInterval.continuous.comp (stdSimplex.continuous_map _))

/-- The actual lower triangle of the specified square map. -/
def lowerTriangle (σ : C(unitInterval × unitInterval, P)) : SingularSimplex P ⦋2⦌ :=
  σ.comp lowerPoint

/-- The actual upper half, with vertex order 00, 01, 11. Its sign in the square is negative. -/
def upperTriangle (σ : C(unitInterval × unitInterval, P)) : SingularSimplex P ⦋2⦌ :=
  σ.comp (ContinuousMap.prodSwap.comp lowerPoint)

/-- The lower horizontal edge is the original first-coordinate axis, with parameter unchanged. -/
theorem lowerTriangle_edge01 (σ : C(unitInterval × unitInterval, P)) (t : unitInterval) :
    lowerTriangle σ (simplexEdgePoint 0 1 t) = σ (t, 0) := by
  change σ (stdSimplexHomeomorphUnitInterval
      (stdSimplex.map lowerFirst (stdSimplex.map (fun k : Fin 2 ↦ if k = 0 then 0 else 1)
        (stdSimplexHomeomorphUnitInterval.symm t))),
    stdSimplexHomeomorphUnitInterval
      (stdSimplex.map lowerSecond (stdSimplex.map (fun k : Fin 2 ↦ if k = 0 then 0 else 1)
        (stdSimplexHomeomorphUnitInterval.symm t)))) = _
  simp only [stdSimplex.map_comp_apply, Function.comp_def]
  have hf : (fun k : Fin 2 ↦ lowerFirst (if k = 0 then 0 else 1)) = id := by
    funext k
    fin_cases k <;> rfl
  have hs : (fun k : Fin 2 ↦ lowerSecond (if k = 0 then 0 else 1)) = fun _ ↦ 0 := by
    funext k
    fin_cases k <;> rfl
  simp only [hf, hs, stdSimplex.map_id_apply, Homeomorph.apply_symm_apply, nativeSimplex_map_const]
  rw [stdSimplexHomeomorphUnitInterval_zero]

/-- The lower vertical edge is the original right boundary, with parameter unchanged. -/
theorem lowerTriangle_edge12 (σ : C(unitInterval × unitInterval, P)) (t : unitInterval) :
    lowerTriangle σ (simplexEdgePoint 1 2 t) = σ (1, t) := by
  change σ (stdSimplexHomeomorphUnitInterval
      (stdSimplex.map lowerFirst (stdSimplex.map (fun k : Fin 2 ↦ if k = 0 then 1 else 2)
        (stdSimplexHomeomorphUnitInterval.symm t))),
    stdSimplexHomeomorphUnitInterval
      (stdSimplex.map lowerSecond (stdSimplex.map (fun k : Fin 2 ↦ if k = 0 then 1 else 2)
        (stdSimplexHomeomorphUnitInterval.symm t)))) = _
  simp only [stdSimplex.map_comp_apply, Function.comp_def]
  have hf : (fun k : Fin 2 ↦ lowerFirst (if k = 0 then 1 else 2)) = fun _ ↦ 1 := by
    funext k
    fin_cases k <;> rfl
  have hs : (fun k : Fin 2 ↦ lowerSecond (if k = 0 then 1 else 2)) = id := by
    funext k
    fin_cases k <;> rfl
  simp only [hf, hs, stdSimplex.map_id_apply, Homeomorph.apply_symm_apply, nativeSimplex_map_const]
  rw [stdSimplexHomeomorphUnitInterval_one]

/-- The upper vertical edge is the original second-coordinate axis. -/
theorem upperTriangle_edge01 (σ : C(unitInterval × unitInterval, P)) (t : unitInterval) :
    upperTriangle σ (simplexEdgePoint 0 1 t) = σ (0, t) :=
  lowerTriangle_edge01 (σ.comp ContinuousMap.prodSwap) t

/-- The upper horizontal edge is the original top boundary. -/
theorem upperTriangle_edge12 (σ : C(unitInterval × unitInterval, P)) (t : unitInterval) :
    upperTriangle σ (simplexEdgePoint 1 2 t) = σ (t, 1) :=
  lowerTriangle_edge12 (σ.comp ContinuousMap.prodSwap) t
/-- Both halves have the same original diagonal parameter. -/
theorem lowerTriangle_edge02 (σ : C(unitInterval × unitInterval, P)) (t : unitInterval) :
    lowerTriangle σ (simplexEdgePoint 0 2 t) = σ (t, t) := by
  change σ (stdSimplexHomeomorphUnitInterval
      (stdSimplex.map lowerFirst (stdSimplex.map (fun k : Fin 2 ↦ if k = 0 then 0 else 2)
        (stdSimplexHomeomorphUnitInterval.symm t))),
    stdSimplexHomeomorphUnitInterval
      (stdSimplex.map lowerSecond (stdSimplex.map (fun k : Fin 2 ↦ if k = 0 then 0 else 2)
        (stdSimplexHomeomorphUnitInterval.symm t)))) = _
  simp only [stdSimplex.map_comp_apply, Function.comp_def]
  have hf : (fun k : Fin 2 ↦ lowerFirst (if k = 0 then 0 else 2)) = id := by
    funext k
    fin_cases k <;> rfl
  have hs : (fun k : Fin 2 ↦ lowerSecond (if k = 0 then 0 else 2)) = id := by
    funext k
    fin_cases k <;> rfl
  simp only [hf, hs, stdSimplex.map_id_apply, Homeomorph.apply_symm_apply]

/-- The diagonal of the upper half is literally the same parametrized diagonal. -/
theorem upperTriangle_edge02 (σ : C(unitInterval × unitInterval, P)) (t : unitInterval) :
    upperTriangle σ (simplexEdgePoint 0 2 t) = σ (t, t) :=
  lowerTriangle_edge02 (σ.comp ContinuousMap.prodSwap) t

/-- A one-dimensional face retains the exact original interval edge parameter. -/
theorem restrictTriangle_interval (τ : SingularSimplex P ⦋2⦌) (i : Fin 3) (t : unitInterval) :
    restrictSimplex τ (SimplexCategory.δ i) (stdSimplexHomeomorphUnitInterval.symm t) =
      τ (simplexEdgePoint (i.succAbove 0) (i.succAbove 1) t) := by
  change τ (stdSimplex.map (SimplexCategory.δ i) (stdSimplexHomeomorphUnitInterval.symm t)) = _
  rw [SimplexCategory.coe_δ]
  apply congrArg τ
  unfold simplexEdgePoint
  congr 1
  funext k
  fin_cases k <;> rfl


/-- The right edge equals the opposite left edge as an original singular one-simplex. -/
theorem periodic_lowerFace_zero (σ : C(unitInterval × unitInterval, P))
    (hFirst : ∀ t, σ (0, t) = σ (1, t)) :
    restrictSimplex (lowerTriangle σ) (SimplexCategory.δ 0) =
      restrictSimplex (upperTriangle σ) (SimplexCategory.δ 2) := by
  ext x
  obtain ⟨t, rfl⟩ := stdSimplexHomeomorphUnitInterval.symm.surjective x
  rw [restrictTriangle_interval, restrictTriangle_interval]
  change lowerTriangle σ (simplexEdgePoint 1 2 t) =
    upperTriangle σ (simplexEdgePoint 0 1 t)
  rw [lowerTriangle_edge12, upperTriangle_edge01]
  exact (hFirst t).symm

/-- The two actual diagonal faces agree with their entire parametrization. -/
theorem periodic_lowerFace_one (σ : C(unitInterval × unitInterval, P)) :
    restrictSimplex (lowerTriangle σ) (SimplexCategory.δ 1) =
      restrictSimplex (upperTriangle σ) (SimplexCategory.δ 1) := by
  ext x
  obtain ⟨t, rfl⟩ := stdSimplexHomeomorphUnitInterval.symm.surjective x
  rw [restrictTriangle_interval, restrictTriangle_interval]
  change lowerTriangle σ (simplexEdgePoint 0 2 t) =
    upperTriangle σ (simplexEdgePoint 0 2 t)
  rw [lowerTriangle_edge02, upperTriangle_edge02]

/-- The bottom edge equals the opposite top edge as an original singular one-simplex. -/
theorem periodic_lowerFace_two (σ : C(unitInterval × unitInterval, P))
    (hSecond : ∀ t, σ (t, 0) = σ (t, 1)) :
    restrictSimplex (lowerTriangle σ) (SimplexCategory.δ 2) =
      restrictSimplex (upperTriangle σ) (SimplexCategory.δ 0) := by
  ext x
  obtain ⟨t, rfl⟩ := stdSimplexHomeomorphUnitInterval.symm.surjective x
  rw [restrictTriangle_interval, restrictTriangle_interval]
  change lowerTriangle σ (simplexEdgePoint 0 1 t) =
    upperTriangle σ (simplexEdgePoint 1 2 t)
  rw [lowerTriangle_edge01, upperTriangle_edge12]
  exact hSecond t

/-- The genuine two triangular boundaries coincide, so their oriented difference is a cycle. -/
theorem periodicSquare_boundary (σ : C(unitInterval × unitInterval, P))
    (hFirst : ∀ t, σ (0, t) = σ (1, t)) (hSecond : ∀ t, σ (t, 0) = σ (t, 1)) :
    chainInclusion (constant P integralCoefficients.{u}) (lowerTriangle σ) ≫
      (singularChainComplex (constant P integralCoefficients.{u})).d 2 1 =
    chainInclusion (constant P integralCoefficients.{u}) (upperTriangle σ) ≫
      (singularChainComplex (constant P integralCoefficients.{u})).d 2 1 := by
  let incl (τ : SingularSimplex P ⦋1⦌) : integralCoefficients.{u} ⟶
      chainModule (constant P integralCoefficients.{u}) ⦋1⦌ :=
    chainInclusion (constant P integralCoefficients.{u}) τ
  rw [chainInclusion_d, chainInclusion_d]
  change (∑ i : Fin 3, (-1 : ℤ) ^ i.val •
    incl (restrictSimplex (lowerTriangle σ) (SimplexCategory.δ i))) =
    ∑ i : Fin 3, (-1 : ℤ) ^ i.val •
      incl (restrictSimplex (upperTriangle σ) (SimplexCategory.δ i))
  norm_num [Fin.sum_univ_succ]
  change incl (restrictSimplex (lowerTriangle σ) (SimplexCategory.δ 0)) +
    (-incl (restrictSimplex (lowerTriangle σ) (SimplexCategory.δ 1)) +
      incl (restrictSimplex (lowerTriangle σ) (SimplexCategory.δ 2))) =
    incl (restrictSimplex (upperTriangle σ) (SimplexCategory.δ 0)) +
    (-incl (restrictSimplex (upperTriangle σ) (SimplexCategory.δ 1)) +
      incl (restrictSimplex (upperTriangle σ) (SimplexCategory.δ 2)))
  rw [periodic_lowerFace_zero σ hFirst, periodic_lowerFace_one,
    periodic_lowerFace_two σ hSecond]
  abel

/-- The positively oriented square is lower triangle minus upper triangle, in original chains. -/
def squareTwoChain (σ : C(unitInterval × unitInterval, P)) :
    (singularChainComplex (constant P integralCoefficients.{u})).X 2 :=
  chainInclusion (constant P integralCoefficients.{u}) (lowerTriangle σ) (ULift.up 1) -
    chainInclusion (constant P integralCoefficients.{u}) (upperTriangle σ) (ULift.up 1)

/-- Its original differential is zero exactly by periodicity of the original square. -/
theorem squareTwoChain_cycle (σ : C(unitInterval × unitInterval, P))
    (hFirst : ∀ t, σ (0, t) = σ (1, t)) (hSecond : ∀ t, σ (t, 0) = σ (t, 1)) :
    (singularChainComplex (constant P integralCoefficients.{u})).d 2 1 (squareTwoChain σ) =
      0 := by
  rw [squareTwoChain, map_sub]
  exact sub_eq_zero.mpr (ConcreteCategory.congr_hom
    (periodicSquare_boundary σ hFirst hSecond) (ULift.up 1))

/-- The original square representative as a genuine categorical singular two-cycle. -/
def squareTwoCycle (σ : C(unitInterval × unitInterval, P))
    (hFirst : ∀ t, σ (0, t) = σ (1, t)) (hSecond : ∀ t, σ (t, 0) = σ (t, 1)) :
    (singularChainComplex (constant P integralCoefficients.{u})).cycles 2 :=
  ((singularChainComplex (constant P integralCoefficients.{u})).sc 2).cyclesMk
    (squareTwoChain σ) (by
      change (singularChainComplex (constant P integralCoefficients.{u})).d 2
        ((ComplexShape.down ℕ).next 2) (squareTwoChain σ) = 0
      rw [show (ComplexShape.down ℕ).next 2 = 1 from ChainComplex.next_nat_succ 1]
      exact squareTwoChain_cycle σ hFirst hSecond)

/-- The cycle is literally the two original triangle generators with signs plus and minus. -/
theorem iCycles_squareTwoCycle (σ : C(unitInterval × unitInterval, P))
    (hFirst : ∀ t, σ (0, t) = σ (1, t)) (hSecond : ∀ t, σ (t, 0) = σ (t, 1)) :
    (singularChainComplex (constant P integralCoefficients.{u})).iCycles 2
      (squareTwoCycle σ hFirst hSecond) = squareTwoChain σ :=
  ((singularChainComplex (constant P integralCoefficients.{u})).sc 2).i_cyclesMk _ _

/-- The first original axis starts and ends at the actual square vertex. -/
def firstAxis (σ : C(unitInterval × unitInterval, P))
    (hFirst : ∀ t, σ (0, t) = σ (1, t)) : Path (σ (0, 0)) (σ (0, 0)) where
  toFun t := σ (t, 0)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := (hFirst 0).symm

/-- The second original axis starts and ends at the same actual square vertex. -/
def secondAxis (σ : C(unitInterval × unitInterval, P))
    (hSecond : ∀ t, σ (t, 0) = σ (t, 1)) : Path (σ (0, 0)) (σ (0, 0)) where
  toFun t := σ (0, t)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := (hSecond 0).symm

/-- The diagonal is the actual diagonal of the same square and returns to its original vertex. -/
def diagonalPath (σ : C(unitInterval × unitInterval, P))
    (hFirst : ∀ t, σ (0, t) = σ (1, t)) (hSecond : ∀ t, σ (t, 0) = σ (t, 1)) :
    Path (σ (0, 0)) (σ (0, 0)) where
  toFun t := σ (t, t)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := (hFirst 1).symm.trans (hSecond 0).symm

/-- The original Pi-one class of the first actual square axis. -/
def firstAxisClass (σ : C(unitInterval × unitInterval, P))
    (hFirst : ∀ t, σ (0, t) = σ (1, t)) : HomotopyGroup.Pi 1 P (σ (0, 0)) :=
  HomotopyGroup.pi1MulEquivFundamentalGroup.symm
    (Path.Homotopic.Quotient.mk (firstAxis σ hFirst))

/-- The original Pi-one class of the second actual square axis. -/
def secondAxisClass (σ : C(unitInterval × unitInterval, P))
    (hSecond : ∀ t, σ (t, 0) = σ (t, 1)) : HomotopyGroup.Pi 1 P (σ (0, 0)) :=
  HomotopyGroup.pi1MulEquivFundamentalGroup.symm
    (Path.Homotopic.Quotient.mk (secondAxis σ hSecond))


end FundamentalGroupoid.LocalCoefficients.SingularBar

end
