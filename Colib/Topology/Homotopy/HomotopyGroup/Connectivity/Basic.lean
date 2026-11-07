/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.WeakCriterion

/-!
# Finite connectivity of an original continuous map

An `n`-connected map has nonempty actual path-space fibers and singleton finite homotopy sets
of those fibers in degrees strictly below `n`, at every actual fiber point. Thus zero connectivity
means surjectivity on components, and weak equivalence means connectivity in every finite range.
The original map is surjective on homotopy sets through degree `n` and bijective below `n`.
In the usual space convention the fibers are `(n - 1)`-connected: their homotopy sets
vanish for `i < n`, rather than for `i ≤ n`. At `n = 0` this means nonempty fibers only;
no natural-number subtraction is used in the definition.
-/

/-! Implementation provenance: adapted from
`Quillen/Topology/HomotopyGroups/Connectivity/Basic.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, finite bounds,
whole path families and universe parameters are retained in their native owners. -/
@[expose] public section

noncomputable section
open Topology TopCat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open scoped Topology unitInterval

universe u

namespace Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Finite connectivity of the unchanged map, with actual nonempty fibers and all basepoints. -/
structure IsHomotopyConnectedMap (f : C(X, Y)) (n : ℕ) : Prop where
  fiber_nonempty : ∀ y : Y, Nonempty (HomotopyFiber f y)
  fiber_subsingleton : ∀ y (z : HomotopyFiber f y) (k : ℕ), k < n →
    Subsingleton (HomotopyGroup.Pi k (HomotopyFiber f y) z)

namespace IsHomotopyConnectedMap

variable {f : C(X, Y)} {n : ℕ} (hf : IsHomotopyConnectedMap f n)
include hf

/-- Lowering the range does not change the original map or any fiber point. -/
theorem mono {m : ℕ} (hmn : m ≤ n) : IsHomotopyConnectedMap f m :=
  ⟨hf.fiber_nonempty, fun y z k hk ↦ hf.fiber_subsingleton y z k (lt_of_lt_of_le hk hmn)⟩

/-- Zero connectivity still includes genuine target-component coverage. -/
theorem component_surjective (y : Y) : ∃ x : X, Joined (f x) y := by
  let z := Classical.choice (hf.fiber_nonempty y)
  exact ⟨z.1.1, ⟨HomotopyFiber.toPath f y z⟩⟩

/-- Every original zero-dimensional homotopy class lifts, even at the endpoint of the range. -/
theorem homotopyGroupMap_zero_surjective (x : X) :
    Function.Surjective (HomotopyGroup.map (N := Fin 0) f (x := x) rfl) := by
  intro b
  induction b using Quotient.inductionOn with
  | h b =>
    obtain ⟨a, ha⟩ := hf.component_surjective (b 0)
    let γ := ha.somePath
    let q : GenLoop (Fin 0) X x :=
      ⟨ContinuousMap.const _ a, by rintro t ⟨i, _⟩; exact Fin.elim0 i⟩
    refine ⟨Quotient.mk' q, Quotient.sound ⟨?_⟩⟩
    exact {
      toFun z := γ z.1
      continuous_toFun := by fun_prop
      map_zero_left _ := γ.source
      map_one_left s := γ.target.trans (congrArg b (Subsingleton.elim 0 s))
      prop' := by rintro t s ⟨i, _⟩; exact Fin.elim0 i }

/-- In positive connectivity, the original map reflects actual component paths. -/
theorem joined_of_image_joined (hn : 0 < n) (x₀ x₁ : X) (h : Joined (f x₀) (f x₁)) :
    Joined x₀ x₁ := by
  let γ := h.somePath
  let a : HomotopyFiber f (f x₁) := ⟨(x₀, γ.toContinuousMap), γ.source, γ.target⟩
  let b := HomotopyFiber.basepoint f (f x₁) x₁ rfl
  let := hf.fiber_subsingleton (f x₁) a 0 hn
  let : Subsingleton (ZerothHomotopy (HomotopyFiber f (f x₁))) :=
    (HomotopyGroup.pi0EquivZerothHomotopy
      (X := HomotopyFiber f (f x₁)) (x := a)).symm.injective.subsingleton
  let : PathConnectedSpace (HomotopyFiber f (f x₁)) :=
    pathConnectedSpace_iff_zerothHomotopy.2 ⟨⟨ZerothHomotopy.mk a⟩, inferInstance⟩
  exact (PathConnectedSpace.joined a b).map (HomotopyFiber.projection f (f x₁)).continuous

/-- The unchanged homotopy map is surjective through the displayed connectivity degree. -/
theorem homotopyGroupMap_surjective (x : X) (k : ℕ) (hk : k ≤ n) :
    Function.Surjective (HomotopyGroup.map (N := Fin k) f (x := x) rfl) := by
  cases k with
  | zero => exact hf.homotopyGroupMap_zero_surjective x
  | succ k =>
    let := hf.fiber_subsingleton (f x) (HomotopyFiber.basepoint f (f x) x rfl) k (by omega)
    intro a
    exact (HomotopyFiber.mem_range_piMap_iff_connectingMap_constant f (f x) x rfl k a).mpr
      (Subsingleton.elim _ _)

/-- Strictly below the range, the original map is bijective at every actual source point. -/
theorem homotopyGroupMap_bijective (x : X) (k : ℕ) (hk : k < n) :
    Function.Bijective (HomotopyGroup.map (N := Fin k) f (x := x) rfl) := by
  cases k with
  | zero =>
    exact homotopyGroupMap_zero_bijective_of_components f hf.component_surjective
      (hf.joined_of_image_joined hk) x
  | succ k =>
    let := hf.fiber_subsingleton (f x) (HomotopyFiber.basepoint f (f x) x rfl) k (by omega)
    let := hf.fiber_subsingleton (f x) (HomotopyFiber.basepoint f (f x) x rfl) (k + 1) hk
    exact HomotopyFiber.piMap_bijective_of_subsingleton_fiber f (f x) x rfl k

end IsHomotopyConnectedMap

/-- The zeroth range is exactly target-component coverage, including empty spaces. -/
theorem isHomotopyConnectedMap_zero_iff (f : C(X, Y)) :
    IsHomotopyConnectedMap f 0 ↔ ∀ y : Y, ∃ x : X, Joined (f x) y := by
  refine ⟨fun hf ↦ hf.component_surjective, fun h ↦ ⟨?_, ?_⟩⟩
  · intro y
    obtain ⟨x, hx⟩ := h y
    exact ⟨⟨(x, hx.somePath.toContinuousMap), hx.somePath.source, hx.somePath.target⟩⟩
  · intro y z k hk
    omega

/-- A complete weak equivalence satisfies every finite connectivity bound on its actual fibers. -/
theorem IsWeakHomotopyEquivalence.isHomotopyConnectedMap {f : C(X, Y)}
    (hf : IsWeakHomotopyEquivalence f) (n : ℕ) : IsHomotopyConnectedMap f n :=
  ⟨HomotopyFiber.nonempty_of_weakEquivalence f hf,
    fun y z k _ ↦ HomotopyFiber.subsingleton_of_weakEquivalence f hf y z k⟩

/-- All finite connectivity bounds recover exactly the original complete weak property. -/
theorem isWeakHomotopyEquivalence_iff_isHomotopyConnectedMap (f : C(X, Y)) :
    IsWeakHomotopyEquivalence f ↔ ∀ n, IsHomotopyConnectedMap f n := by
  refine ⟨fun hf n ↦ hf.isHomotopyConnectedMap n, fun hf ↦ ?_⟩
  exact HomotopyFiber.isWeakHomotopyEquivalence_of_fibers f (hf 0).fiber_nonempty
    (fun y z k ↦ (hf (k + 1)).fiber_subsingleton y z k (Nat.lt_succ_self k))

end Topology
