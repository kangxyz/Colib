/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyPullback.WeakSource
public import Colib.Topology.HomotopyPullback.Pasting

/-! # Pasting original weak-cartesian squares

The prescribed outer comparison factors through the original nested
comparison. Uniform weak source change and the actual nested-pullback
homotopy equivalence then give the complete weak conclusion by cancellation.


Implementation provenance:
`Quillen/Topology/HomotopyPullback/WeakPasting.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology
universe u
namespace Topology.HomotopyPullback
variable {X₀ X₁ X₂ B₀ B₁ B₂ : Type u}
  [TopologicalSpace X₀] [TopologicalSpace X₁] [TopologicalSpace X₂]
  [TopologicalSpace B₀] [TopologicalSpace B₁] [TopologicalSpace B₂]
  (p₀ : C(X₀, B₀)) (p₁ : C(X₁, B₁)) (p₂ : C(X₂, B₂))
  (a : C(X₀, X₁)) (a' : C(X₁, X₂)) (b : C(B₀, B₁)) (b' : C(B₁, B₂))
  (w : p₁.comp a = b.comp p₀) (w' : p₂.comp a' = b'.comp p₁)

/-- The actual nested-coordinate map carries the original outer comparison
to the original composite comparison, including both complete paths. -/
theorem pastingComparison_factorization :
    (pastingIntoNestedEquiv p₂ b b').toFun.comp
      (comparison p₂ (b'.comp b) p₀ (a'.comp a) (pasteSquare p₀ p₁ p₂ a a' b b' w w')) =
      (sourceMap b (baseProjection p₂ b') (comparison p₂ b' p₁ a' w')).comp
        (comparison p₁ b p₀ a w) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · exact (ContinuousMap.congr_fun w x).symm
      · apply Prod.ext
        · rfl
        · apply ContinuousMap.ext
          intro t
          exact congrArg b' (ContinuousMap.congr_fun w x).symm
    · rfl

/-- Two original weak-cartesian squares paste, with the canonical outer
constant-path comparison and complete empty-aware weak property. -/
theorem comparison_paste_isWeakHomotopyEquivalence
    (h : IsWeakHomotopyEquivalence (comparison p₁ b p₀ a w))
    (h' : IsWeakHomotopyEquivalence (comparison p₂ b' p₁ a' w')) :
    IsWeakHomotopyEquivalence
      (comparison p₂ (b'.comp b) p₀ (a'.comp a) (pasteSquare p₀ p₁ p₂ a a' b b' w w')) := by
  have hcomp := (sourceMap_isWeakHomotopyEquivalence b (baseProjection p₂ b')
    (comparison p₂ b' p₁ a' w') h').comp h
  rw [← pastingComparison_factorization p₀ p₁ p₂ a a' b b' w w'] at hcomp
  exact hcomp.of_comp_right (isWeakHomotopyEquivalence_of_homotopyEquiv
    (pastingIntoNestedEquiv p₂ b b'))

end Topology.HomotopyPullback
