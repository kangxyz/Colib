/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Homotopy.IntervalEndpoints

/-!
# Parameter-preserving cylinder extension

The explicit simplex-boundary extension never changes its external
parameter. Consequently it preserves any prescribed map to a base space.
This supplies the fiberwise endpoint extension needed for the thick
mapping-cylinder construction in the homotopy-cartesian gluing argument.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/MappingCylinder/Fiberwise/Basic.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual maps and hypotheses. -/
@[expose] public section

open Convexity


noncomputable section

open Topology
open CategoryTheory Limits MonoidalCategory StdSimplex
open scoped Topology unitInterval
open unitInterval

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace TopCat

/-- The explicit simplex extension preserves every parameterwise invariant
shared by its initial and boundary data. -/
theorem simplexBoundaryHomotopyExtension_invariant
    {X Y W : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (f : C(X × StdSimplex ℝ (Fin (n + 1)), Y))
    (H : C((X × StdSimplex.boundary n) × I, Y))
    (h : ∀ x b, H ((x, b), 0) = f (x, b.1))
    (q : Y → W) (base : X → W)
    (hf : ∀ x b, q (f (x, b)) = base x)
    (hH : ∀ x b t, q (H ((x, b), t)) = base x)
    (x : X) (b : StdSimplex ℝ (Fin (n + 1))) (t : I) :
    q (simplexBoundaryHomotopyExtension n f H h ((x, b), t)) = base x := by
  change q (closedCylinderGlueFun (StdSimplex.boundary n) f H
    (x, simplexBoundaryCylinderRetraction n (b, t))) = base x
  unfold closedCylinderGlueFun
  split_ifs
  · exact hH _ _ _
  · exact hf _ _

/-- The endpoint-pair coordinate homeomorphism retains the external parameter. -/
theorem intervalEndpointDomainHomeomorph_symm_parameter
    (X : Type u) [TopologicalSpace X] (x : X) (b : StdSimplex.boundary 1) :
    Sum.elim id id ((TopCat.intervalEndpointDomainHomeomorph X).symm (x, b)) = x := by
  classical
  change Sum.elim id id (if b = StdSimplex.boundaryZero then Sum.inl x else Sum.inr x) = x
  split_ifs <;> rfl

/-- Initial interval data in one-simplex coordinates. -/
def intervalEndpointInitial {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X × I, Y)) : C(X × StdSimplex ℝ (Fin 2), Y) :=
  ⟨fun z ↦ f (z.1, StdSimplex.homeomorphI z.2), by fun_prop⟩

/-- Endpoint homotopies in one-simplex-boundary coordinates. -/
def intervalEndpointSide {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (H : C((X ⊕ X) × I, Y)) : C((X × StdSimplex.boundary 1) × I, Y) :=
  ⟨fun z ↦ H ((TopCat.intervalEndpointDomainHomeomorph X).symm z.1, z.2), by fun_prop⟩

theorem intervalEndpoint_compatible
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X × I, Y)) (H : C((X ⊕ X) × I, Y))
    (h₀ : ∀ x, H (Sum.inl x, 0) = f (x, 0))
    (h₁ : ∀ x, H (Sum.inr x, 0) = f (x, 1)) :
    ∀ x b, intervalEndpointSide H ((x, b), 0) = intervalEndpointInitial f (x, b.1) := by
  intro x b
  rcases StdSimplex.boundary_eq_zero_or_one b with rfl | rfl
  · change H ((TopCat.intervalEndpointDomainHomeomorph X).symm
      ((TopCat.intervalEndpointDomainHomeomorph X) (Sum.inl x)), 0) =
      f (x, StdSimplex.homeomorphI (StdSimplex.single 0))
    rw [Homeomorph.symm_apply_apply, StdSimplex.homeomorphI_single_zero]
    exact h₀ x
  · change H ((TopCat.intervalEndpointDomainHomeomorph X).symm
      ((TopCat.intervalEndpointDomainHomeomorph X) (Sum.inr x)), 0) =
      f (x, StdSimplex.homeomorphI (StdSimplex.single 1))
    rw [Homeomorph.symm_apply_apply, StdSimplex.homeomorphI_single_one]
    exact h₁ x

/-- The exact interval endpoint extension operator obtained from the
proved one-simplex boundary operator. -/
def intervalEndpointExtension
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X × I, Y)) (H : C((X ⊕ X) × I, Y))
    (h₀ : ∀ x, H (Sum.inl x, 0) = f (x, 0))
    (h₁ : ∀ x, H (Sum.inr x, 0) = f (x, 1)) : C((X × I) × I, Y) :=
  (simplexBoundaryHomotopyExtension 1 (intervalEndpointInitial f) (intervalEndpointSide H)
    (intervalEndpoint_compatible f H h₀ h₁)).comp
      ⟨fun z ↦ ((z.1.1, StdSimplex.homeomorphI.symm z.1.2), z.2), by fun_prop⟩

variable {X Y W : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X × I, Y)) (H : C((X ⊕ X) × I, Y))
  (h₀ : ∀ x, H (Sum.inl x, 0) = f (x, 0))
  (h₁ : ∀ x, H (Sum.inr x, 0) = f (x, 1))

@[simp]
theorem intervalEndpointExtension_zero (x : X) (s : I) :
    intervalEndpointExtension f H h₀ h₁ ((x, s), 0) = f (x, s) := by
  change simplexBoundaryHomotopyExtension 1 (intervalEndpointInitial f) (intervalEndpointSide H)
    (intervalEndpoint_compatible f H h₀ h₁) ((x, StdSimplex.homeomorphI.symm s), 0) = _
  rw [simplexBoundaryHomotopyExtension_zero]
  change f (x, StdSimplex.homeomorphI (StdSimplex.homeomorphI.symm s)) = _
  rw [Homeomorph.apply_symm_apply]

@[simp]
theorem intervalEndpointExtension_left (x : X) (t : I) :
    intervalEndpointExtension f H h₀ h₁ ((x, 0), t) = H (Sum.inl x, t) := by
  change simplexBoundaryHomotopyExtension 1 (intervalEndpointInitial f) (intervalEndpointSide H)
    (intervalEndpoint_compatible f H h₀ h₁) ((x, StdSimplex.homeomorphI.symm 0), t) = _
  have he : StdSimplex.homeomorphI.symm 0 = (StdSimplex.boundaryZero).1 := by
    apply StdSimplex.homeomorphI.injective
    rw [Homeomorph.apply_symm_apply]
    exact StdSimplex.homeomorphI_single_zero.symm
  rw [he, simplexBoundaryHomotopyExtension_side]
  change H ((TopCat.intervalEndpointDomainHomeomorph X).symm
    ((TopCat.intervalEndpointDomainHomeomorph X) (Sum.inl x)), t) = _
  rw [Homeomorph.symm_apply_apply]

@[simp]
theorem intervalEndpointExtension_right (x : X) (t : I) :
    intervalEndpointExtension f H h₀ h₁ ((x, 1), t) = H (Sum.inr x, t) := by
  change simplexBoundaryHomotopyExtension 1 (intervalEndpointInitial f) (intervalEndpointSide H)
    (intervalEndpoint_compatible f H h₀ h₁) ((x, StdSimplex.homeomorphI.symm 1), t) = _
  have he : StdSimplex.homeomorphI.symm 1 = (StdSimplex.boundaryOne).1 := by
    apply StdSimplex.homeomorphI.injective
    rw [Homeomorph.apply_symm_apply]
    exact StdSimplex.homeomorphI_single_one.symm
  rw [he, simplexBoundaryHomotopyExtension_side]
  change H ((TopCat.intervalEndpointDomainHomeomorph X).symm
    ((TopCat.intervalEndpointDomainHomeomorph X) (Sum.inr x)), t) = _
  rw [Homeomorph.symm_apply_apply]

/-- Parameter-preserving endpoint extension: a common base map remains
unchanged throughout the entire extension. -/
theorem intervalEndpointExtension_invariant (q : Y → W) (base : X → W)
    (hf : ∀ x s, q (f (x, s)) = base x)
    (hH : ∀ a t, q (H (a, t)) = base (Sum.elim id id a)) (x : X) (s t : I) :
    q (intervalEndpointExtension f H h₀ h₁ ((x, s), t)) = base x := by
  change q (simplexBoundaryHomotopyExtension 1 (intervalEndpointInitial f)
    (intervalEndpointSide H) (intervalEndpoint_compatible f H h₀ h₁)
    ((x, StdSimplex.homeomorphI.symm s), t)) = _
  apply simplexBoundaryHomotopyExtension_invariant
  · intro x b
    exact hf x _
  · intro x b t
    change q (H ((TopCat.intervalEndpointDomainHomeomorph X).symm (x, b), t)) = base x
    rw [hH, intervalEndpointDomainHomeomorph_symm_parameter]

end TopCat
