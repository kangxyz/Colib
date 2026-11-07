/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.Homology
public import Mathlib.Algebra.Category.ModuleCat.Products

/-!
Adapted from `Quillen/Topology/LocalCoefficients/ChainSupport.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining its actual coefficient maps.

# Finite support of actual twisted singular chains

The categorical coproduct is identified with the actual dependent direct sum.
Thus every chain, and a cycle representing every homology class, uses finitely
many genuine singular simplices with coefficients at their first vertices.
-/

@[expose] public section
noncomputable section
open CategoryTheory Limits
open scoped Simplicial DirectSum
universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local instance 2000] DirectSum.instModule

namespace FundamentalGroupoid.LocalCoefficients
variable {X : Type u} [TopologicalSpace X] (A : System.{u, u} X)

/-- Actual finite-support coordinates, retaining the individual coefficient fibers. -/
def chainCoordinatesIso (n : SimplexCategory) :
    chainModule A n ≅ ModuleCat.of ℤ (⨁ σ : SingularSimplex X n, simplexFiber A σ) := by
  classical
  exact ModuleCat.coprodIsoDirectSum (fun σ : SingularSimplex X n ↦ simplexFiber A σ)

/-- Inclusion of a simplex agrees with its actual direct-sum summand. -/
@[reassoc]
theorem chainInclusion_coordinates (n : SimplexCategory) (σ : SingularSimplex X n) :
    chainInclusion A σ ≫ (chainCoordinatesIso A n).hom =
      ModuleCat.ofHom (DirectSum.lof ℤ (SingularSimplex X n)
        (fun τ ↦ (simplexFiber A τ : Type u)) σ) := by
  classical
  exact ModuleCat.ι_coprodIsoDirectSum_hom _ σ

/-- Every actual twisted chain is a finite sum of genuine simplex inclusions. -/
theorem chain_exists_finite_sum (n : SimplexCategory) (x : chainModule A n) :
    ∃ (s : Finset (SingularSimplex X n)) (a : ∀ σ, simplexFiber A σ),
      x = ∑ σ ∈ s, chainInclusion A σ (a σ) := by
  classical
  let e := chainCoordinatesIso A n
  let y := e.hom x
  refine ⟨y.support, fun σ ↦ y σ, ?_⟩
  apply e.toLinearEquiv.injective
  change e.hom.hom x = e.hom.hom (∑ σ ∈ y.support, chainInclusion A σ (y σ))
  rw [map_sum]
  have h (σ : SingularSimplex X n) :
      e.hom (chainInclusion A σ (y σ)) = DirectSum.of (fun σ ↦ simplexFiber A σ) σ (y σ) :=
    ConcreteCategory.congr_hom (chainInclusion_coordinates A n σ) (y σ)
  simp_rw [h]
  exact (DirectSum.sum_support_of y).symm

/-- The effect of any coefficient map on a fixed chain is determined at finitely
many actual first vertices. No constancy of the system is required. -/
theorem chain_exists_finite_test_set (n : SimplexCategory) (x : chainModule A n) :
    ∃ s : Finset (SingularSimplex X n), ∀ (B : System.{u, u} X) (η θ : A ⟶ B),
      (∀ σ ∈ s, η.app (FundamentalGroupoid.mk (σ (Convexity.StdSimplex.single 0))) =
        θ.app (FundamentalGroupoid.mk (σ (Convexity.StdSimplex.single 0)))) →
      coefficientModuleMap η n x = coefficientModuleMap θ n x := by
  classical
  obtain ⟨s, a, rfl⟩ := chain_exists_finite_sum A n x
  refine ⟨s, fun B η θ h ↦ ?_⟩
  change (coefficientModuleMap η n).hom (∑ σ ∈ s, chainInclusion A σ (a σ)) =
    (coefficientModuleMap θ n).hom (∑ σ ∈ s, chainInclusion A σ (a σ))
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  have hη := ConcreteCategory.congr_hom (chainInclusion_coefficientModuleMap η σ) (a σ)
  have hθ := ConcreteCategory.congr_hom (chainInclusion_coefficientModuleMap θ σ) (a σ)
  change coefficientModuleMap η n (chainInclusion A σ (a σ)) =
    coefficientModuleMap θ n (chainInclusion A σ (a σ))
  exact hη.trans ((congrArg (fun f ↦ chainInclusion B σ (f (a σ))) (h σ hσ)).trans hθ.symm)

/-- Every homology class has a cycle whose underlying chain is explicitly
supported on finitely many actual singular simplices. -/
theorem homology_exists_finite_cycle (n : ℕ) (x : homology A n) :
    ∃ (z : (singularChainComplex A).cycles n)
      (s : Finset (SingularSimplex X ⦋n⦌)) (a : ∀ σ, simplexFiber A σ),
      (singularChainComplex A).homologyπ n z = x ∧
      (singularChainComplex A).iCycles n z = ∑ σ ∈ s, chainInclusion A σ (a σ) := by
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective
    ((singularChainComplex A).homologyπ n)).mp inferInstance x
  obtain ⟨s, a, ha⟩ := chain_exists_finite_sum A ⦋n⦌ ((singularChainComplex A).iCycles n z)
  exact ⟨z, s, a, hz, ha⟩

/-- A fixed homology class tests coefficient transformations at only finitely
many vertices. This is the finite support needed for monodromy corrections. -/
theorem homology_exists_finite_test_set (n : ℕ) (x : homology A n) :
    ∃ s : Finset (SingularSimplex X ⦋n⦌), ∀ (B : System.{u, u} X) (η θ : A ⟶ B),
      (∀ σ ∈ s, η.app (FundamentalGroupoid.mk (σ (Convexity.StdSimplex.single 0))) =
        θ.app (FundamentalGroupoid.mk (σ (Convexity.StdSimplex.single 0)))) →
      coefficientHomologyMap η n x = coefficientHomologyMap θ n x := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((singularChainComplex A).homologyπ n)).mp inferInstance x
  obtain ⟨s, hs⟩ := chain_exists_finite_test_set A ⦋n⦌
    ((singularChainComplex A).iCycles n z)
  refine ⟨s, fun B η θ h ↦ ?_⟩
  have hz : HomologicalComplex.cyclesMap (coefficientChainMap η) n z =
      HomologicalComplex.cyclesMap (coefficientChainMap θ) n z := by
    apply (ModuleCat.mono_iff_injective ((singularChainComplex B).iCycles n)).mp
      inferInstance
    have hη := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (coefficientChainMap η) n) z
    have hθ := ConcreteCategory.congr_hom
      (HomologicalComplex.cyclesMap_i (coefficientChainMap θ) n) z
    exact hη.trans ((hs B η θ h).trans hθ.symm)
  have hη := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (coefficientChainMap η) n) z
  have hθ := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (coefficientChainMap θ) n) z
  exact hη.trans ((congrArg ((singularChainComplex B).homologyπ n) hz).trans hθ.symm)

end FundamentalGroupoid.LocalCoefficients
