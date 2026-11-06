/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalence

/-! # Weak homotopy equivalences, including empty source spaces

Based homotopy-set bijectivity at every source point is vacuous for an empty
source. The property below separately requires actual surjectivity on path
components, so an empty source cannot be weakly equivalent to a nonempty target.
No continuous family of inverse maps is part of this property.
-/
/-! The empty-aware property and its basic laws are extracted from source
`Quillen/Topology/HomotopyGroups/WeakEquivalenceProperty.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, with actual maps and component paths retained. -/
@[expose] public section

noncomputable section
open scoped Topology unitInterval
universe u v w
namespace Topology
variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The original map is onto actual path components and bijective on every
finite based homotopy set. The component clause controls empty spaces. -/
structure IsWeakHomotopyEquivalence (f : C(X, Y)) : Prop where
  component_surjective : ∀ y : Y, ∃ x : X, Joined (f x) y
  homotopy_bijective : ∀ x : X, ∀ n : ℕ,
    Function.Bijective (HomotopyGroup.map (N := Fin n) f (x := x) rfl)

/-- At an actual supplied point, surjectivity of the original π₀ map implies
surjectivity on every target path component. -/
theorem component_surjective_of_homotopyGroupMap_zero_surjective
    (f : C(X, Y)) (x₀ : X)
    (h : Function.Surjective (HomotopyGroup.map (N := Fin 0) f (x := x₀) rfl)) :
    ∀ y : Y, ∃ x : X, Joined (f x) y := by
  intro y
  let q : GenLoop (Fin 0) Y (f x₀) :=
    ⟨ContinuousMap.const _ y, by rintro t ⟨i, _⟩; exact Fin.elim0 i⟩
  obtain ⟨a, ha⟩ := h (Quotient.mk' q)
  induction a using Quotient.inductionOn with | h a =>
    obtain ⟨H⟩ := Quotient.exact ha
    exact ⟨a 0, ⟨H.toHomotopy.evalAt 0⟩⟩

/-- A genuine chosen point rules out the empty-source loophole. -/
theorem isWeakHomotopyEquivalence_of_point
    (f : C(X, Y)) (x₀ : X)
    (h : ∀ x : X, ∀ n : ℕ,
      Function.Bijective (HomotopyGroup.map (N := Fin n) f (x := x) rfl)) :
    IsWeakHomotopyEquivalence f :=
  ⟨component_surjective_of_homotopyGroupMap_zero_surjective f x₀ (h x₀ 0).surjective, h⟩

/-- A weak equivalence with empty source has genuinely empty target. -/
theorem IsWeakHomotopyEquivalence.isEmpty_target {f : C(X, Y)}
    (h : IsWeakHomotopyEquivalence f) [IsEmpty X] : IsEmpty Y :=
  ⟨fun y => by obtain ⟨x, _⟩ := h.component_surjective y; exact isEmptyElim x⟩

/-- Composition retains the actual component paths and original homotopy maps. -/
theorem IsWeakHomotopyEquivalence.comp {f : C(X, Y)} {g : C(Y, Z)}
    (hg : IsWeakHomotopyEquivalence g) (hf : IsWeakHomotopyEquivalence f) :
    IsWeakHomotopyEquivalence (g.comp f) where
  component_surjective z := by
    obtain ⟨y, hy⟩ := hg.component_surjective z
    obtain ⟨x, hx⟩ := hf.component_surjective y
    exact ⟨x, (hx.map g.continuous).trans hy⟩
  homotopy_bijective x n := homotopyGroupMap_bijective_comp f g rfl rfl n
    (hf.homotopy_bijective x n) (hg.homotopy_bijective (f x) n)

/-- An actual homotopy equivalence yields this empty-aware weak property with
its original forward map. -/
theorem isWeakHomotopyEquivalence_of_homotopyEquiv
    (e : ContinuousMap.HomotopyEquiv X Y) : IsWeakHomotopyEquivalence e.toFun where
  component_surjective y := by
    obtain ⟨H⟩ := e.right_inv
    exact ⟨e.invFun y, ⟨H.evalAt y⟩⟩
  homotopy_bijective x n := homotopyGroupMap_bijective_of_homotopyEquiv e rfl n

/-- The actual identity map satisfies the complete property, even on empty spaces. -/
theorem isWeakHomotopyEquivalence_id (X : Type u) [TopologicalSpace X] :
    IsWeakHomotopyEquivalence (ContinuousMap.id X) :=
  isWeakHomotopyEquivalence_of_homotopyEquiv (ContinuousMap.HomotopyEquiv.refl X)


end Topology
