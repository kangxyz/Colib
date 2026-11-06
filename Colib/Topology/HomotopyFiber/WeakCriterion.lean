/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.WeakFibers
public import Colib.Topology.Homotopy.HomotopyGroup.ComponentCriterion

/-! # Weak equivalences detected by all actual homotopy fibers

Nonemptiness is explicit, so this criterion covers empty spaces correctly.
The component proof uses actual paths in the actual homotopy fiber; positive
degrees use the original long exact sequence.


Implementation provenance:
`Quillen/Topology/HomotopyFiber/WeakCriterion.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u
namespace Topology.HomotopyFiber
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Nonempty, weakly contractible actual fibers detect the original weak
 equivalence, including its component surjectivity and original π₀ map. -/
theorem isWeakHomotopyEquivalence_of_fibers (f : C(X, Y))
    (hne : ∀ y, Nonempty (HomotopyFiber f y))
    (hsub : ∀ y (z : HomotopyFiber f y) (n : ℕ),
      Subsingleton (HomotopyGroup.Pi n (HomotopyFiber f y) z)) :
    IsWeakHomotopyEquivalence f := by
  have hs : ∀ y, ∃ x, Joined (f x) y := by
    intro y
    let z := Classical.choice (hne y)
    exact ⟨z.1.1, ⟨toPath f y z⟩⟩
  have hj : ∀ x₀ x₁, Joined (f x₀) (f x₁) → Joined x₀ x₁ := by
    intro x₀ x₁ h
    let γ := h.somePath
    let a : HomotopyFiber f (f x₁) := ⟨(x₀, γ.toContinuousMap), γ.source, γ.target⟩
    let b := basepoint f (f x₁) x₁ rfl
    let := hsub (f x₁) a 0
    let : Subsingleton (ZerothHomotopy (HomotopyFiber f (f x₁))) :=
      (HomotopyGroup.pi0EquivZerothHomotopy (X := HomotopyFiber f (f x₁)) (x :=
        a)).symm.injective.subsingleton
    let : PathConnectedSpace (HomotopyFiber f (f x₁)) :=
      pathConnectedSpace_iff_zerothHomotopy.2 ⟨⟨ZerothHomotopy.mk a⟩, inferInstance⟩
    exact (PathConnectedSpace.joined a b).map (projection f (f x₁)).continuous
  refine ⟨hs, ?_⟩
  intro x n
  cases n with
  | zero => exact homotopyGroupMap_zero_bijective_of_components f hs hj x
  | succ n =>
    let := hsub (f x) (basepoint f (f x) x rfl) n
    let := hsub (f x) (basepoint f (f x) x rfl) (n + 1)
    exact piMap_bijective_of_subsingleton_fiber f (f x) x rfl n

/-- Exact original-map characterization by the genuine path-space fibers. -/
theorem isWeakHomotopyEquivalence_iff_fibers (f : C(X, Y)) :
    IsWeakHomotopyEquivalence f ↔
      (∀ y, Nonempty (HomotopyFiber f y)) ∧
      (∀ y (z : HomotopyFiber f y) (n : ℕ),
        Subsingleton (HomotopyGroup.Pi n (HomotopyFiber f y) z)) :=
  ⟨fun hf => ⟨nonempty_of_weakEquivalence f hf, subsingleton_of_weakEquivalence f hf⟩,
    fun h => isWeakHomotopyEquivalence_of_fibers f h.1 h.2⟩

end Topology.HomotopyFiber
