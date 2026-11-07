/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.IntegralChains
public import Colib.Topology.LocalCoefficients.SubspaceChains
public import Mathlib.Algebra.Module.ULift
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Evaluation of actual integral singular chains in an abelian group

The integral coefficient module is the universe-correct lift of the integers.
An arbitrary value on each actual singular simplex extends by the coproduct
universal property. Vanishing on the basepoint-constant simplex makes this map
kill the genuine point-subspace chain inclusion. These are purely algebraic
constructions; no homotopy-addition theorem or Hurewicz statement is assumed.
-/

/-! Implementation source: `Quillen/Topology/LocalCoefficients/IntegralChainEvaluation.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, basepoints,
coefficients and signs are retained with native Colib dependencies. -/
@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace FundamentalGroupoid.LocalCoefficients

variable {X : Type u} [TopologicalSpace X]
variable {G : Type u} [AddCommGroup G]

/-- Send one lifted integral coefficient to the corresponding multiple of g. -/
def integralMultiple (g : G) : integralCoefficients.{u} ⟶ ModuleCat.of ℤ G :=
  ModuleCat.ofHom ((LinearMap.toSpanSingleton ℤ G g).comp
    (ULift.moduleEquiv : ULift.{u} ℤ ≃ₗ[ℤ] ℤ).toLinearMap)

@[simp] theorem integralMultiple_apply (g : G) (a : ULift.{u} ℤ) :
    integralMultiple g a = a.down • g := rfl

/-- The actual coproduct extension of values on all singular simplices. -/
def integralChainEvaluation (n : ℕ) (v : SingularSimplex X ⦋n⦌ → G) :
    chainModule (constant X integralCoefficients.{u}) ⦋n⦌ ⟶ ModuleCat.of ℤ G :=
  Sigma.desc fun τ ↦ integralMultiple (v τ)

/-- Evaluation on a genuine simplex summand retains its integral coefficient. -/
@[reassoc]
theorem chainInclusion_integralChainEvaluation (n : ℕ)
    (v : SingularSimplex X ⦋n⦌ → G) (τ : SingularSimplex X ⦋n⦌) :
    chainInclusion (constant X integralCoefficients.{u}) τ ≫
      integralChainEvaluation n v = integralMultiple (v τ) :=
  by simp [chainInclusion, integralChainEvaluation]

@[simp] theorem integralChainEvaluation_inclusion (n : ℕ)
    (v : SingularSimplex X ⦋n⦌ → G) (τ : SingularSimplex X ⦋n⦌) (a : ULift.{u} ℤ) :
    integralChainEvaluation n v
      (chainInclusion (constant X integralCoefficients.{u}) τ a) = a.down • v τ :=
  ConcreteCategory.congr_hom (chainInclusion_integralChainEvaluation n v τ) a

/-- Evaluation of finite chains is the literal finite integral linear combination. -/
theorem integralChainEvaluation_sum (n : ℕ) (v : SingularSimplex X ⦋n⦌ → G)
    (b : Finset (SingularSimplex X ⦋n⦌)) (a : ∀ _τ, ULift.{u} ℤ) :
    integralChainEvaluation n v
      (∑ τ ∈ b, chainInclusion (constant X integralCoefficients.{u}) τ (a τ)) =
      ∑ τ ∈ b, (a τ).down • v τ := by
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro τ hτ
  exact integralChainEvaluation_inclusion n v τ (a τ)

/-- Constant integral coefficients have no residual first-face transport. -/
theorem integralRestrictionTransport {d e : SimplexCategory}
    (τ : SingularSimplex X e) (α : d ⟶ e) :
    restrictionTransport (constant X integralCoefficients.{u}) τ α =
      𝟙 integralCoefficients.{u} := rfl

/-- The original alternating chain differential uses exactly the standard face
signs; the zeroth face has the same constant coefficient as every other face. -/
theorem chainInclusion_d_integralChainEvaluation (n : ℕ)
    (v : SingularSimplex X ⦋n⦌ → G) (τ : SingularSimplex X ⦋n + 1⦌) :
    chainInclusion (constant X integralCoefficients.{u}) τ ≫
      (singularChainComplex (constant X integralCoefficients.{u})).d (n + 1) n ≫
        integralChainEvaluation n v =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        integralMultiple (v (restrictSimplex τ (SimplexCategory.δ i))) := by
  rw [chainInclusion_d_assoc]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc,
    chainInclusion_integralChainEvaluation, integralRestrictionTransport]
  apply Finset.sum_congr rfl
  intro i _
  congr 1

/-- Elementwise boundary evaluation, retaining both the original integer
coefficient and every standard alternating face sign. -/
theorem integralChainEvaluation_boundary (n : ℕ)
    (v : SingularSimplex X ⦋n⦌ → G) (τ : SingularSimplex X ⦋n + 1⦌) (a : ULift.{u} ℤ) :
    integralChainEvaluation n v
      ((singularChainComplex (constant X integralCoefficients.{u})).d (n + 1) n
        (chainInclusion (constant X integralCoefficients.{u}) τ a)) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        (a.down • v (restrictSimplex τ (SimplexCategory.δ i))) := by
  let ev : (integralCoefficients.{u} ⟶ ModuleCat.of ℤ G) →+ G := {
    toFun f := f.hom a
    map_zero' := rfl
    map_add' _ _ := rfl }
  calc
    _ = ev (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        integralMultiple (v (restrictSimplex τ (SimplexCategory.δ i)))) :=
      congrArg ev (chainInclusion_d_integralChainEvaluation n v τ)
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_zsmul]
      rfl

/-- Every simplex in the one-point subspace pushes forward to the basepoint
constant simplex, with its coefficient unchanged. -/
theorem subspacePoint_comp_eq_const (z : X) (n : ℕ)
    (τ : SingularSimplex ({z} : Set X) ⦋n⦌) :
    (subspaceInclusion {z}).comp τ = ContinuousMap.const _ z := by
  ext x
  exact (τ x).property

/-- Evaluation killing the basepoint constant also kills every genuine point chain. -/
theorem pointPushforward_integralChainEvaluation (z : X) (n : ℕ)
    (v : SingularSimplex X ⦋n⦌ → G) (hv : v (ContinuousMap.const _ z) = 0) :
    pushforwardModuleMap (subspaceInclusion {z}) (constant X integralCoefficients.{u}) ⦋n⦌ ≫
      integralChainEvaluation n v = 0 := by
  apply Sigma.hom_ext
  intro τ
  change chainInclusion _ τ ≫
    (pushforwardModuleMap (subspaceInclusion {z}) _ ⦋n⦌ ≫ integralChainEvaluation n v) = _
  rw [chainInclusion_pushforwardModuleMap_assoc, subspacePoint_comp_eq_const,
    chainInclusion_integralChainEvaluation, hv]
  ext a
  change a.down • (0 : G) = 0
  exact smul_zero _

end FundamentalGroupoid.LocalCoefficients
