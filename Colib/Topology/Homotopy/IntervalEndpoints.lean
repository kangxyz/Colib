/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Analysis.Convex.StdSimplex.FaceCharts
public import Colib.Topology.Realization.SimplexBoundaryHEP
public import Colib.Topology.Realization.SimplexBoundaryEndpoints
public import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex
public import Mathlib.Topology.Piecewise
public import Mathlib.Tactic.FinCases
public import Mathlib.Topology.Separation.Basic

/-!
# Homotopy extension for both interval endpoints
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/HELP/IntervalEndpoints.lean` at
commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, homotopies and
pushout universal properties are retained, with native namespace and import ownership.
-/
@[expose] public section

open Convexity


noncomputable section

open CategoryTheory MonoidalCategory StdSimplex
open scoped Topology unitInterval

universe u

namespace TopCat

attribute [local instance] Classical.propDecidable

local instance : Finite (boundary 1) := by
  apply Finite.of_surjective (fun b : Bool ↦ if b then StdSimplex.boundaryOne else
    StdSimplex.boundaryZero)
  intro b
  rcases StdSimplex.boundary_eq_zero_or_one b with rfl | rfl
  · exact ⟨false, rfl⟩
  · exact ⟨true, rfl⟩

local instance : DiscreteTopology (boundary 1) := inferInstance

/-- The disjoint union of two copies of a space is its product with the simplex boundary. -/
def intervalEndpointDomainHomeomorph (A : Type u) [TopologicalSpace A] :
    (A ⊕ A) ≃ₜ A × boundary 1 where
  toFun := Sum.elim (fun a ↦ (a, StdSimplex.boundaryZero)) (fun a ↦ (a, StdSimplex.boundaryOne))
  invFun z := if z.2 = StdSimplex.boundaryZero then Sum.inl z.1 else Sum.inr z.1
  left_inv a := by
    cases a <;> simp [StdSimplex.boundaryZero_ne_one.symm]
  right_inv z := by
    rcases z with ⟨a, b⟩
    rcases StdSimplex.boundary_eq_zero_or_one b with rfl | rfl <;>
      simp [StdSimplex.boundaryZero_ne_one.symm]
  continuous_toFun := continuous_sum_dom.mpr ⟨by fun_prop, by fun_prop⟩
  continuous_invFun := by
    apply continuous_if
    · intro z hz
      have hc : IsClopen {z : A × boundary 1 | z.2 = StdSimplex.boundaryZero} :=
        (isClopen_discrete {StdSimplex.boundaryZero}).preimage continuous_snd
      rw [hc.frontier_eq] at hz
      exact False.elim hz
    · exact (continuous_inl.comp continuous_fst).continuousOn
    · exact (continuous_inr.comp continuous_fst).continuousOn

/-- The usual inclusion of both endpoints in a topological cylinder. -/
def intervalEndpoints (A : TopCat.{u}) : TopCat.of (A ⊕ A) ⟶ A ⊗ TopCat.I :=
  TopCat.ofHom ⟨Sum.elim (fun a ↦ (a, ULift.up 0)) (fun a ↦ (a, ULift.up 1)),
    continuous_sum_dom.mpr ⟨by fun_prop, by fun_prop⟩⟩

/-- The endpoint pair inclusion has HEP after product with any space. -/
theorem homotopyExtensionProperty_intervalEndpoints (A : TopCat.{u}) :
    TopCat.HomotopyExtensionProperty (TopCat.intervalEndpoints A) := by
  let e₁ : TopCat.of (A ⊕ A) ≅ TopCat.of (A × boundary 1) :=
    TopCat.isoOfHomeo (TopCat.intervalEndpointDomainHomeomorph A)
  let e₂ : TopCat.of (A × StdSimplex ℝ (Fin 2)) ≅ A ⊗ TopCat.I :=
    TopCat.isoOfHomeo ((Homeomorph.refl A).prodCongr
      (StdSimplex.homeomorphI.trans TopCat.I.homeomorph.symm))
  have h := TopCat.homotopyExtensionProperty_comp
    (TopCat.homotopyExtensionProperty_comp
      (TopCat.homotopyExtensionProperty_of_isIso e₁.hom)
      (TopCat.homotopyExtensionProperty_simplexBoundary A 1))
    (TopCat.homotopyExtensionProperty_of_isIso e₂.hom)
  have heq : (e₁.hom ≫ TopCat.parameterizedSimplexBoundaryInclusion A 1) ≫ e₂.hom =
      TopCat.intervalEndpoints A := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro a
    cases a with
    | inl a =>
      change (a, ULift.up (StdSimplex.homeomorphI (StdSimplex.single 0))) =
        (a, ULift.up 0)
      rw [StdSimplex.homeomorphI_single_zero]
    | inr a =>
      change (a, ULift.up (StdSimplex.homeomorphI (StdSimplex.single 1))) =
        (a, ULift.up 1)
      rw [StdSimplex.homeomorphI_single_one]
  exact heq ▸ h


end TopCat
