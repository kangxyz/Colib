/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.SubspaceChains

/-!
# Singular chains supported on a union of path components

The actual subspace inclusion is an isomorphism when every excluded simplex
fiber vanishes. Path saturation reduces that condition to support of fibers.
Adapted from `Quillen/Topology/LocalCoefficients/SupportedChains.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using a direct summand restriction.
-/

@[expose] public section
noncomputable section
open CategoryTheory Limits
open scoped Simplicial
universe u
namespace FundamentalGroupoid.LocalCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {X : Type u} [TopologicalSpace X]

/-- Vanishing discarded fibers makes restriction a right inverse as well. -/
theorem subspaceModuleProjection_inclusion_of_support
    (U : Set X) (A : System.{u, u} X) (n : SimplexCategory)
    (hA : ∀ σ : SingularSimplex X n, ¬ Set.range σ ⊆ U → IsZero (simplexFiber A σ)) :
    subspaceModuleProjection U A n ≫ pushforwardModuleMap (subspaceInclusion U) A n = 𝟙 _ := by
  classical
  apply Sigma.hom_ext
  intro σ
  by_cases hσ : Set.range σ ⊆ U
  · change chainInclusion A σ ≫
        (subspaceModuleProjection U A n ≫ pushforwardModuleMap (subspaceInclusion U) A n) =
      chainInclusion A σ ≫ 𝟙 _
    rw [chainInclusion_subspaceModuleProjection_assoc, dite_eq_left hσ,
      chainInclusion_pushforwardModuleMap, Category.comp_id]
    rfl
  · exact (hA σ hσ).eq_of_src _ _

/-- The actual spatial chain map is an isomorphism when discarded fibers vanish. -/
theorem subspaceInclusion_pushforwardChainMap_isIso_of_simplex_support
    (U : Set X) (A : System.{u, u} X)
    (hA : ∀ (n : SimplexCategory) (σ : SingularSimplex X n),
      ¬ Set.range σ ⊆ U → IsZero (simplexFiber A σ)) :
    IsIso (pushforwardChainMap (subspaceInclusion U) A) := by
  have h : ∀ n : ℕ, IsIso ((pushforwardChainMap (subspaceInclusion U) A).f n) := by
    intro n
    change IsIso (pushforwardModuleMap (subspaceInclusion U) A ⦋n⦌)
    exact ⟨⟨subspaceModuleProjection U A ⦋n⦌, subspaceInclusion_projection U A ⦋n⦌,
      subspaceModuleProjection_inclusion_of_support U A ⦋n⦌ (hA ⦋n⦌)⟩⟩
  exact HomologicalComplex.Hom.isIso_of_components _

/-- A simplex with first vertex in a path-saturated set lies entirely in it. -/
theorem simplex_range_subset_of_path_saturated (U : Set X)
    (hU : ∀ a ∈ U, ∀ b, Joined a b → b ∈ U)
    {n : SimplexCategory} (σ : SingularSimplex X n)
    (hσ : σ (stdSimplex.vertex 0) ∈ U) : Set.range σ ⊆ U := by
  rintro _ ⟨t, rfl⟩
  exact hU _ hσ _ ⟨(PathConnectedSpace.somePath (stdSimplex.vertex 0) t).map σ.continuous⟩

/-- Supported coefficients identify the actual chains of a path-saturated subspace. -/
theorem subspaceInclusion_pushforwardChainMap_isIso_of_support (U : Set X)
    (hU : ∀ a ∈ U, ∀ b, Joined a b → b ∈ U) (A : System.{u, u} X)
    (hA : ∀ x, x ∉ U → IsZero (fiber A x)) :
    IsIso (pushforwardChainMap (subspaceInclusion U) A) := by
  apply subspaceInclusion_pushforwardChainMap_isIso_of_simplex_support
  intro n σ hσ
  apply hA
  intro h
  exact hσ (simplex_range_subset_of_path_saturated U hU σ h)

/-- The inclusion of a component is an isomorphism for coefficients supported there. -/
theorem pathComponentInclusion_pushforwardChainMap_isIso_of_support
    (x : X) (A : System.{u, u} X)
    (hA : ∀ y, y ∉ pathComponent x → IsZero (fiber A y)) :
    IsIso (pushforwardChainMap (subspaceInclusion (pathComponent x)) A) :=
  subspaceInclusion_pushforwardChainMap_isIso_of_support (pathComponent x)
    (fun _ ha _ hab ↦ hab.mem_pathComponent ha) A hA

end FundamentalGroupoid.LocalCoefficients
