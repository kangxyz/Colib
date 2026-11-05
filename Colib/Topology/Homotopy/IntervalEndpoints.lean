/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.SimplexBoundaryHEP
public import Mathlib.Topology.Piecewise
public import Mathlib.Tactic.FinCases
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex

/-!
# Homotopy extension for both interval endpoints
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/HELP/IntervalEndpoints.lean` at
commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, homotopies and
pushout universal properties are retained, with native namespace and import ownership.
-/
@[expose] public section


noncomputable section

open CategoryTheory MonoidalCategory Convexity Convexity.StdSimplex
open scoped Topology unitInterval

universe u

namespace TopCat

attribute [local instance] Classical.propDecidable

/-- The two vertices are all points of the geometric one-simplex boundary. -/
theorem simplexBoundary_one_cases (b : simplexBoundary 1) :
    b.1 = StdSimplex.single 0 ∨ b.1 = StdSimplex.single 1 := by
  have hs : b.1.weights 0 + b.1.weights 1 = 1 := by
    simp
  obtain ⟨i, hi⟩ := b.2
  fin_cases i
  · right
    change b.1.weights 0 = 0 at hi
    have h1 : b.1.weights 1 = 1 := by linarith
    apply StdSimplex.ext
    ext j
    fin_cases j <;> simp [hi, h1]
  · left
    change b.1.weights 1 = 0 at hi
    have h0 : b.1.weights 0 = 1 := by linarith
    apply StdSimplex.ext
    ext j
    fin_cases j <;> simp [hi, h0]

/-- The first interval endpoint as a simplex-boundary point. -/
def boundaryZero : simplexBoundary 1 :=
  ⟨StdSimplex.single 0, ⟨1, by simp⟩⟩

/-- The second interval endpoint as a simplex-boundary point. -/
def boundaryOne : simplexBoundary 1 :=
  ⟨StdSimplex.single 1, ⟨0, by simp⟩⟩

lemma boundaryZero_ne_one : TopCat.boundaryZero ≠ TopCat.boundaryOne := by
  intro h
  have h' := congrArg (fun b : simplexBoundary 1 ↦ StdSimplex.homeomorphI b.1) h
  simp [TopCat.boundaryZero, TopCat.boundaryOne] at h'

lemma boundary_eq_zero_or_one (b : simplexBoundary 1) : b = TopCat.boundaryZero ∨ b =
  TopCat.boundaryOne := by
  rcases TopCat.simplexBoundary_one_cases b with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

local instance : Finite (simplexBoundary 1) := by
  apply Finite.of_surjective (fun b : Bool ↦ if b then TopCat.boundaryOne else
    TopCat.boundaryZero)
  intro b
  rcases TopCat.boundary_eq_zero_or_one b with rfl | rfl
  · exact ⟨false, rfl⟩
  · exact ⟨true, rfl⟩

local instance : T2Space (StdSimplex ℝ (Fin (1 + 1))) :=
  (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin 2)).t2Space

local instance : T2Space (simplexBoundary 1) := inferInstance
local instance : DiscreteTopology (simplexBoundary 1) := inferInstance

/-- The disjoint union of two copies of a space is its product with the simplex boundary. -/
def intervalEndpointDomainHomeomorph (A : Type u) [TopologicalSpace A] :
    (A ⊕ A) ≃ₜ A × simplexBoundary 1 where
  toFun := Sum.elim (fun a ↦ (a, TopCat.boundaryZero)) (fun a ↦ (a, TopCat.boundaryOne))
  invFun z := if z.2 = TopCat.boundaryZero then Sum.inl z.1 else Sum.inr z.1
  left_inv a := by
    cases a <;> simp [TopCat.boundaryZero_ne_one.symm]
  right_inv z := by
    rcases z with ⟨a, b⟩
    rcases TopCat.boundary_eq_zero_or_one b with rfl | rfl <;>
      simp [TopCat.boundaryZero_ne_one.symm]
  continuous_toFun := continuous_sum_dom.mpr ⟨by fun_prop, by fun_prop⟩
  continuous_invFun := by
    apply continuous_if
    · intro z hz
      have hc : IsClopen {z : A × simplexBoundary 1 | z.2 = TopCat.boundaryZero} :=
        (isClopen_discrete {TopCat.boundaryZero}).preimage continuous_snd
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
  let e₁ : TopCat.of (A ⊕ A) ≅ TopCat.of (A × simplexBoundary 1) :=
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
      change (a, ULift.up (StdSimplex.homeomorphI (StdSimplex.single 0))) = (a, ULift.up 0)
      rw [StdSimplex.homeomorphI_single_zero]
    | inr a =>
      change (a, ULift.up (StdSimplex.homeomorphI (StdSimplex.single 1))) = (a, ULift.up 1)
      rw [StdSimplex.homeomorphI_single_one]
  exact heq ▸ h


end TopCat
