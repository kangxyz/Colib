/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.CommonBaseSquare
public import Colib.Topology.HomotopyPullback.WeakSource

/-! # Transport of the original common-base comparison through actual fiber models

Two given weak fiber-model comparisons, with their actual projection and
transition squares, identify the original model square as weakly homotopy
cartesian. The proof uses the original common-base homotopy equivalence and
the established weak source-change theorem, retaining the original constant
comparison path. No global relative-realization fiber comparison is supplied
or inferred for any particular Waldhausen model here.


Implementation provenance:
`Quillen/Topology/HomotopyFiber/CommonBaseSquareTransport.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open scoped Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Topology.HomotopyFiber
section PullbackMap
variable {F X Y B : Type u} [TopologicalSpace F] [TopologicalSpace X]
  [TopologicalSpace Y] [TopologicalSpace B]
  (q : C(Y, B)) (j : C(X, Y)) (b : B) (f : C(F, Y))
  (k : C(F, HomotopyFiber q b)) (hk : (projection q b).comp k = f)

/-- The actual source-change map after a displayed projection equality.
Its parameter and complete outer path are unchanged. -/
def fiberModelPullbackMap : C(HomotopyPullback f j, HomotopyPullback (projection q b) j) where
  toFun z := ⟨(z.1.1, k z.1.2.1, z.1.2.2),
    z.2.1.trans (ContinuousMap.congr_fun hk z.1.2.1).symm, z.2.2⟩
  continuous_toFun := by fun_prop

@[simp] theorem fiberModelPullbackMap_parameter (z : HomotopyPullback f j) :
    (fiberModelPullbackMap q j b f k hk z).1.1 = z.1.1 := rfl

@[simp] theorem fiberModelPullbackMap_source (z : HomotopyPullback f j) :
    (fiberModelPullbackMap q j b f k hk z).1.2.1 = k z.1.2.1 := rfl

@[simp] theorem fiberModelPullbackMap_path (z : HomotopyPullback f j) :
    (fiberModelPullbackMap q j b f k hk z).1.2.2 = z.1.2.2 := rfl

/-- The displayed source comparison is exactly the already established
source-change map when its projection equality is literal. -/
@[simp] theorem fiberModelPullbackMap_eq_sourceMap :
    fiberModelPullbackMap q j b ((projection q b).comp k) k rfl =
      HomotopyPullback.sourceMap j (projection q b) k := rfl

/-- Weakness follows from genuine weak source invariance, with unchanged paths. -/
theorem fiberModelPullbackMap_isWeakHomotopyEquivalence
    (h : IsWeakHomotopyEquivalence k) :
    IsWeakHomotopyEquivalence (fiberModelPullbackMap q j b f k hk) := by
  subst f
  exact HomotopyPullback.sourceMap_isWeakHomotopyEquivalence j (projection q b) k h
end PullbackMap

section Comparison
variable {A F X Y B : Type u} [TopologicalSpace A] [TopologicalSpace F]
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace B]
  (p : C(X, B)) (q : C(Y, B)) (j : C(X, Y)) (sq : q.comp j = p) (b : B)
  (a : C(A, X)) (f : C(F, Y)) (i : C(A, F)) (w : f.comp i = j.comp a)
  (k₀ : C(A, HomotopyFiber p b)) (k₁ : C(F, HomotopyFiber q b))
  (h₀ : (projection p b).comp k₀ = a) (h₁ : (projection q b).comp k₁ = f)
  (hc : (mapOver p q j sq b).comp k₀ = k₁.comp i)

include h₀ hc in
/-- The two original comparison maps commute strictly under the actual fiber
models. The complete stored path and the constant outer path both agree. -/
theorem fiberModelComparison_factorization :
    (fiberModelPullbackMap q j b f k₁ h₁).comp (HomotopyPullback.comparison f j a i w) =
      (commonBaseComparison p q j sq b).comp k₀ := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · exact (ContinuousMap.congr_fun h₀ x).symm
  · apply Prod.ext
    · exact (ContinuousMap.congr_fun hc x).symm
    · apply ContinuousMap.ext
      intro t
      exact congrArg j (ContinuousMap.congr_fun h₀ x).symm

include sq h₀ h₁ hc in
/-- The two actual weak fiber-model comparisons imply weakness of the
original model-square comparison. The two weak inputs remain explicit;
no statement about a global relative-tail model is assumed implicitly. -/
theorem fiberModelComparison_isWeakHomotopyEquivalence
    (hk₀ : IsWeakHomotopyEquivalence k₀) (hk₁ : IsWeakHomotopyEquivalence k₁) :
    IsWeakHomotopyEquivalence (HomotopyPullback.comparison f j a i w) := by
  have h := (isWeakHomotopyEquivalence_of_homotopyEquiv
    (commonBaseComparisonEquiv p q j sq b)).comp hk₀
  change IsWeakHomotopyEquivalence ((commonBaseComparison p q j sq b).comp k₀) at h
  rw [← fiberModelComparison_factorization p q j sq b a f i w k₀ k₁ h₀ h₁ hc] at h
  exact h.of_comp_right (fiberModelPullbackMap_isWeakHomotopyEquivalence q j b f k₁ h₁ hk₁)

end Comparison
end Topology.HomotopyFiber
