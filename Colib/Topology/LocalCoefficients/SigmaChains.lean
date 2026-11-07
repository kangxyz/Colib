/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.Functoriality
public import Mathlib.Topology.ContinuousMap.Sigma
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
Adapted from `Quillen/Topology/LocalCoefficients/SigmaChains.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps.

# Twisted singular chains on arbitrary disjoint unions

Every actual singular simplex in a topological disjoint union lies in one unique
summand. Reindexing these genuine simplices gives a chain isomorphism from the
coproduct of the restricted twisted chain complexes. Its summand maps are the
original spatial maps of the disjoint-union inclusions.
-/

@[expose] public section

open Convexity
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits
open scoped Simplicial
universe u
namespace FundamentalGroupoid.LocalCoefficients

variable {ι : Type u} (X : ι → Type u) [∀ i, TopologicalSpace (X i)]

/-- Connectedness of the geometric simplex gives the actual summand parametrization. -/
def sigmaSimplexEquiv (n : SimplexCategory) :
    (Σ i, SingularSimplex (X i) n) ≃ SingularSimplex (Σ i, X i) n :=
  (ContinuousMap.sigmaCodHomeomorph (StdSimplex ℝ (Fin (n.len + 1))) X).toEquiv.symm

@[simp]
theorem sigmaSimplexEquiv_apply (n : SimplexCategory) (i : ι)
    (σ : SingularSimplex (X i) n) :
    sigmaSimplexEquiv X n ⟨i, σ⟩ = (ContinuousMap.sigmaMk i).comp σ := rfl

/-- Degreewise decomposition into genuine singular simplices of the summands. -/
def sigmaChainModuleIso (A : System.{u, u} (Σ i, X i)) (n : SimplexCategory) :
    (∐ fun i ↦ chainModule (pullback (ContinuousMap.sigmaMk i) A) n) ≅ chainModule A n :=
  sigmaSigmaIso (fun i ↦ SingularSimplex (X i) n)
      (fun i σ ↦ simplexFiber (pullback (ContinuousMap.sigmaMk i) A) σ) ≪≫
    Sigma.whiskerEquiv (f := fun t : Σ i, SingularSimplex (X i) n ↦
        simplexFiber (pullback (ContinuousMap.sigmaMk t.1) A) t.2)
      (g := fun σ : SingularSimplex (Σ i, X i) n ↦ simplexFiber A σ)
      (sigmaSimplexEquiv X n) (fun _ ↦ Iso.refl _)

/-- The original sum of the spatial module maps of the summand inclusions. -/
def sigmaPushforwardModuleMap (A : System.{u, u} (Σ i, X i)) (n : SimplexCategory) :
    (∐ fun i ↦ chainModule (pullback (ContinuousMap.sigmaMk i) A) n) ⟶ chainModule A n :=
  Sigma.desc fun i ↦ pushforwardModuleMap (ContinuousMap.sigmaMk i) A n

/-- The degreewise decomposition keeps the specified original inclusion maps. -/
theorem sigmaChainModuleIso_hom (A : System.{u, u} (Σ i, X i)) (n : SimplexCategory) :
    (sigmaChainModuleIso X A n).hom = sigmaPushforwardModuleMap X A n := by
  apply Sigma.hom_ext
  intro i
  apply Sigma.hom_ext
  intro σ
  simp only [pullback_fiber, ContinuousMap.sigmaMk_apply, chainModule, sigmaChainModuleIso,
    sigmaSimplexEquiv, Homeomorph.coe_symm_toEquiv, ContinuousMap.sigmaCodHomeomorph_symm_apply,
    Iso.trans_hom, sigmaSigmaIso_hom, Sigma.whiskerEquiv_hom, Iso.refl_inv,
    colimit.ι_desc_assoc, Discrete.functor_obj_eq_as, Cofan.mk_pt, Cofan.mk_ι_app,
    Sigma.ι_comp_map', sigmaPushforwardModuleMap, pushforwardModuleMap, chainInclusion,
    colimit.ι_desc]
  exact Category.id_comp _

/-- The original coproduct map is invertible in every singular degree. -/
instance sigmaPushforwardModuleMap_isIso (A : System.{u, u} (Σ i, X i)) (n : SimplexCategory) :
    IsIso (sigmaPushforwardModuleMap X A n) := by
  rw [← sigmaChainModuleIso_hom]
  infer_instance

/-- The actual chain map from the coproduct of restricted twisted chain complexes. -/
def sigmaPushforwardChainMap (A : System.{u, u} (Σ i, X i)) :
    (∐ fun i ↦ singularChainComplex (pullback (ContinuousMap.sigmaMk i) A)) ⟶
      singularChainComplex A :=
  Sigma.desc fun i ↦ pushforwardChainMap (ContinuousMap.sigmaMk i) A

/-- Evaluation of the original chain map is the explicit simplex decomposition. -/
theorem sigmaPushforwardChainMap_comparison (A : System.{u, u} (Σ i, X i)) (n : ℕ) :
    sigmaComparison (HomologicalComplex.eval (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) n)
        (fun i ↦ singularChainComplex (pullback (ContinuousMap.sigmaMk i) A)) ≫
      (sigmaPushforwardChainMap X A).f n = sigmaPushforwardModuleMap X A ⦋n⦌ :=
  sigmaComparison_map_desc _ _ _ _

/-- Every component of the original coproduct chain map is an isomorphism. -/
instance sigmaPushforwardChainMap_f_isIso (A : System.{u, u} (Σ i, X i)) (n : ℕ) :
    IsIso ((sigmaPushforwardChainMap X A).f n) :=
  IsIso.of_isIso_fac_left (sigmaPushforwardChainMap_comparison X A n)

/-- The actual twisted chain complex of a disjoint union is the actual coproduct. -/
instance sigmaPushforwardChainMap_isIso (A : System.{u, u} (Σ i, X i)) :
    IsIso (sigmaPushforwardChainMap X A) :=
  HomologicalComplex.Hom.isIso_of_components _

/-- The decomposition retains the original coproduct chain map as its forward map. -/
def sigmaChainComplexIso (A : System.{u, u} (Σ i, X i)) :
    (∐ fun i ↦ singularChainComplex (pullback (ContinuousMap.sigmaMk i) A)) ≅
      singularChainComplex A :=
  asIso (sigmaPushforwardChainMap X A)

/-- The summand equations are the original spatial maps, with no replacement map. -/
@[reassoc (attr := simp)]
theorem sigmaChainComplexIso_inclusion (A : System.{u, u} (Σ i, X i)) (i : ι) :
    Sigma.ι (fun j ↦ singularChainComplex (pullback (ContinuousMap.sigmaMk j) A)) i ≫
      (sigmaChainComplexIso X A).hom = pushforwardChainMap (ContinuousMap.sigmaMk i) A :=
  Sigma.ι_comp_desc _ _

end FundamentalGroupoid.LocalCoefficients
