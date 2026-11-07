/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.TwoSidedBar.ZeroFiber
public import Colib.KTheory.Waldhausen.Fibration.RelativeRows.TotalFiber
public import Colib.KTheory.Waldhausen.Fibration.RelativeRows.TransitionCartesian
public import Colib.Topology.HomotopyFiber.Congruence
public import Colib.CategoryTheory.TheoremB.VertexWeakAssembly
public import Colib.CategoryTheory.TheoremB.ReplacementProjectionTower

/-!
# The original global relative-tail fiber comparison

The actual relative-row transition comparisons and the genuine chosen-zero
row fiber inclusion supply the two-sided bar's zero-row fiber theorem.
Evaluation recovers the original total fiber inclusion, including its entire
constant path. Hence the unchanged `totalTailFiberComparison` is weak in all
finite degrees, including components, without an assumed global fiber theorem.


Implementation provenance:
`Quillen/Waldhausen/Fibration/RelativeRows/WeakTotalFiber.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.TheoremA
open SSet.TwoSidedBar



noncomputable section
open Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open scoped Simplicial Topology
universe u
namespace CategoryTheory.Waldhausen.Fibration.RelativeRows
open TheoremA SSet SSet.TwoSidedBar CategoryTheory.TheoremB.Skeletal
variable {C : Type u} [SmallCategory C] {V : Structure C}
  (N : NestedWeakEquivalences V)

/-- The original row section is weak in every finite dimension, including components. -/
theorem rowFiberInclusion_isWeakHomotopyEquivalence (n : SimplexCategory) :
    IsWeakHomotopyEquivalence (rowFiberInclusion N n) :=
  isWeakHomotopyEquivalence_of_point (rowFiberInclusion N n) V.kBasepoint
    (rowFiberInclusion_bijective N n)

/-- The original ordinal transition comparisons supply the universe-aligned bar input. -/
theorem liftedTail_transitionWeakCartesian :
    TransitionWeakCartesian (Functor.whiskerLeft indexProjection (tailSRows N)) := by
  intro d e f
  exact rowTransitionComparison_isWeakHomotopyEquivalence N (indexProjection.map f)

/-- The constant zero-row chain evaluates to the unchanged original total fiber inclusion. -/
theorem zeroDiagonalInclusion_totalFiberInclusion :
    (fiberSRows N).app (op ⦋0⦌) ≫ zeroDiagonalInclusion (relativeSRows N) =
      totalFiberInclusion N :=
  barZeroInclusion_evaluation_section (fiberSRows N)

/-- The original global tail fiber comparison is weak, with its original source and constant
path. -/
theorem totalTailFiberComparison_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence (totalTailFiberComparison N) := by
  let b := SSet.realizationPoint (tailZeroVertex N ⦋0⦌)
  let e₀ := HomotopyFiber.congrHomeomorph (rowFiberProjection_eq N ⦋0⦌) (rfl : b = b)
  let e₁ := HomotopyFiber.congrHomeomorph
    (rfl : (SSet.toTop.map (diagonalMap (tailSRows N))).hom = totalTailMap N)
    (evaluation_barZero_realizationPoint (ordinarySRows (acyclicStructure N))
      (tailZeroVertex N ⦋0⦌))
  have h := (isWeakHomotopyEquivalence_of_homotopyEquiv e₁.toHomotopyEquiv).comp
    ((zeroDiagonalFiberMap_isWeakHomotopyEquivalence (tailSRows N)
      (liftedTail_transitionWeakCartesian N) b).comp
      ((isWeakHomotopyEquivalence_of_homotopyEquiv e₀.toHomotopyEquiv).comp
        (rowFiberInclusion_isWeakHomotopyEquivalence N ⦋0⦌)))
  have heq : totalTailFiberComparison N = e₁.toHomotopyEquiv.toFun.comp
      ((zeroDiagonalFiberMap (tailSRows N) b).comp
        (e₀.toHomotopyEquiv.toFun.comp (rowFiberInclusion N ⦋0⦌))) := by
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    apply Prod.ext
    · change SSet.toTop.map (totalFiberInclusion N) x =
        SSet.toTop.map (evaluationMap (relativeSRows N))
          (SSet.toTop.map (barZeroInclusion (relativeSRows N))
            (SSet.toTop.map ((fiberSRows N).app (op ⦋0⦌)) x))
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        ← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (fun f ↦ SSet.toTop.map f x)
        (barZeroInclusion_evaluation_section (fiberSRows N)).symm
    · apply ContinuousMap.ext
      intro t
      exact (evaluation_barZero_realizationPoint (ordinarySRows (acyclicStructure N))
        (tailZeroVertex N ⦋0⦌)).symm
  rw [heq]
  exact h

/-- Every original finite based total comparison is bijective, including components. -/
theorem totalTailFiberComparison_bijective (x : V.Delooping) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) (totalTailFiberComparison N)
      (x := x) rfl) :=
  (totalTailFiberComparison_isWeakHomotopyEquivalence N).homotopy_bijective x n

end CategoryTheory.Waldhausen.Fibration.RelativeRows


namespace CategoryTheory.Waldhausen.Fibration.RelativeRows

attribute [colib_tag "COL-0253",
  colib_ref "Waldhausen1985" "Section 1.6, proof of Theorem 1.6.4, relative S-construction"
    "adaptation"
    "Original relative-row total-tail fiber comparison, proved through weak-cartesian \
    realization and the two-sided bar"]
  totalTailFiberComparison_isWeakHomotopyEquivalence

end CategoryTheory.Waldhausen.Fibration.RelativeRows
