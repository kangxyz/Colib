/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.UnitInterval
public import Mathlib.Topology.Homotopy.Equiv

/-! # Evaluation on the actual compact-open free path space

Implementation source: the evaluation and postcomposition constructions from
`Quillen/Topology/HomotopyGroups/PathTransport.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. These use actual continuous-map spaces;
no alternate path model is introduced.
-/
@[expose] public section

noncomputable section
open scoped Topology unitInterval
universe u v
namespace Topology
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Evaluation on the free path space with its actual compact-open topology. -/
def freePathEvaluation (X : Type u) [TopologicalSpace X] (t : unitInterval) :
    C(C(unitInterval, X), X) :=
  ⟨fun p => p t, continuous_eval_const t⟩

/-- Evaluation at any interval point is a homotopy equivalence.  Its inverse
is the actual constant-path map; the inverse homotopy contracts the interval
linearly to the evaluation point. -/
def freePathEvaluationHomotopyEquiv (X : Type u) [TopologicalSpace X]
    (t : unitInterval) : ContinuousMap.HomotopyEquiv C(unitInterval, X) X where
  toFun := freePathEvaluation X t
  invFun := ContinuousMap.const'
  left_inv := ⟨{
    toFun z := ⟨fun s => z.2 (Set.Icc.convexComb t s z.1), by fun_prop⟩
    continuous_toFun := by
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact continuous_fst.snd.eval
        (Set.Icc.continuous_convexComb_prod.comp
          (continuous_const.prodMk (continuous_snd.prodMk continuous_fst.fst)))
    map_zero_left p := by ext s; simp [freePathEvaluation]
    map_one_left p := by ext s; simp }⟩
  right_inv := by
    have h : (freePathEvaluation X t).comp ContinuousMap.const' =
        ContinuousMap.id X := by ext x; rfl
    rw [h]

/-- Actual postcomposition on the free path spaces. -/
def freePathPostcomp (f : C(X, Y)) : C(C(unitInterval, X), C(unitInterval, Y)) :=
  ⟨fun p => f.comp p, ContinuousMap.continuous_postcomp f⟩

@[simp]
theorem freePathEvaluation_postcomp (f : C(X, Y)) (t : unitInterval) :
    (freePathEvaluation Y t).comp (freePathPostcomp f) =
      f.comp (freePathEvaluation X t) := rfl


end Topology
