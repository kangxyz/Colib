/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.RelativeChains

/-!
Adapted from `Quillen/Topology/LocalCoefficients/RelativeCoefficients.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual maps and pullbacks.


# Coefficient maps on actual relative twisted singular chains

Natural transformations of local systems induce maps of the original relative
singular complexes, defined as actual cokernels of the subspace inclusions.
The quotient equations retain the original absolute coefficient maps. Identity
and composition follow by cancellation of the cokernel projections, and provide
a coefficient functor and its canonical isomorphisms.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits

universe u

namespace FundamentalGroupoid.LocalCoefficients

variable {X : Type u} [TopologicalSpace X]

/-- A coefficient morphism induces the actual map of relative singular complexes. -/
def relativeCoefficientChainMap (U : Set X) {A B : System.{u, u} X} (η : A ⟶ B) :
    relativeSingularChainComplex U A ⟶ relativeSingularChainComplex U B :=
  cokernel.map _ _ (coefficientChainMap (pullbackMap (subspaceInclusion U) η))
    (coefficientChainMap η)
    (pushforwardChainMap_coefficient_naturality (subspaceInclusion U) η).symm

/-- The relative coefficient map retains the exact original absolute coefficient map. -/
@[reassoc]
theorem relativeCoefficientChainMap_quotient (U : Set X)
    {A B : System.{u, u} X} (η : A ⟶ B) :
    cokernel.π (pushforwardChainMap (subspaceInclusion U) A) ≫
        relativeCoefficientChainMap U η =
      coefficientChainMap η ≫
        cokernel.π (pushforwardChainMap (subspaceInclusion U) B) := by
  exact cokernel.π_desc _ _ _

/-- The identity coefficient morphism gives the identity on the actual quotient. -/
@[simp]
theorem relativeCoefficientChainMap_id (U : Set X) (A : System.{u, u} X) :
    relativeCoefficientChainMap U (𝟙 A) = 𝟙 (relativeSingularChainComplex U A) := by
  apply (cancel_epi (cokernel.π (pushforwardChainMap (subspaceInclusion U) A))).mp
  dsimp only [relativeSingularChainComplex]
  rw [relativeCoefficientChainMap_quotient, Category.comp_id]
  have hi : coefficientChainMap (𝟙 A) = 𝟙 (singularChainComplex A) :=
    (coefficientChainFunctor X).map_id A
  rw [hi, Category.id_comp]

/-- Composition of coefficient morphisms is preserved by the original relative maps. -/
@[reassoc]
theorem relativeCoefficientChainMap_comp (U : Set X) {A B D : System.{u, u} X}
    (η : A ⟶ B) (θ : B ⟶ D) :
    relativeCoefficientChainMap U (η ≫ θ) =
      relativeCoefficientChainMap U η ≫ relativeCoefficientChainMap U θ := by
  apply (cancel_epi (cokernel.π (pushforwardChainMap (subspaceInclusion U) A))).mp
  dsimp only [relativeSingularChainComplex]
  rw [relativeCoefficientChainMap_quotient,
    relativeCoefficientChainMap_quotient_assoc,
    relativeCoefficientChainMap_quotient, ← Category.assoc]
  exact congrArg (fun k ↦ k ≫ cokernel.π (pushforwardChainMap (subspaceInclusion U) D))
    ((coefficientChainFunctor X).map_comp η θ)

/-- Relative singular chains form a functor in the original local coefficient system. -/
def relativeCoefficientChainFunctor (U : Set X) :
    System.{u, u} X ⥤ ChainComplex (ModuleCat.{u} ℤ) ℕ where
  obj A := relativeSingularChainComplex U A
  map η := relativeCoefficientChainMap U η
  map_id A := relativeCoefficientChainMap_id U A
  map_comp η θ := relativeCoefficientChainMap_comp U η θ

/-- An invertible coefficient morphism induces an invertible map of actual quotients. -/
instance relativeCoefficientChainMap_isIso (U : Set X)
    {A B : System.{u, u} X} (η : A ⟶ B) [IsIso η] :
    IsIso (relativeCoefficientChainMap U η) := by
  change IsIso ((relativeCoefficientChainFunctor U).map η)
  infer_instance

/-- An isomorphism of local systems gives a canonical isomorphism of actual quotients. -/
def relativeCoefficientChainIso (U : Set X) {A B : System.{u, u} X} (e : A ≅ B) :
    relativeSingularChainComplex U A ≅ relativeSingularChainComplex U B :=
  (relativeCoefficientChainFunctor U).mapIso e

/-- The canonical relative coefficient isomorphism has the original quotient equation. -/
@[reassoc]
theorem relativeCoefficientChainIso_hom_quotient (U : Set X)
    {A B : System.{u, u} X} (e : A ≅ B) :
    cokernel.π (pushforwardChainMap (subspaceInclusion U) A) ≫
        (relativeCoefficientChainIso U e).hom =
      coefficientChainMap e.hom ≫
        cokernel.π (pushforwardChainMap (subspaceInclusion U) B) :=
  relativeCoefficientChainMap_quotient U e.hom

/-- The inverse comparison also retains its original absolute coefficient map. -/
@[reassoc]
theorem relativeCoefficientChainIso_inv_quotient (U : Set X)
    {A B : System.{u, u} X} (e : A ≅ B) :
    cokernel.π (pushforwardChainMap (subspaceInclusion U) B) ≫
        (relativeCoefficientChainIso U e).inv =
      coefficientChainMap e.inv ≫
        cokernel.π (pushforwardChainMap (subspaceInclusion U) A) :=
  relativeCoefficientChainMap_quotient U e.inv

end FundamentalGroupoid.LocalCoefficients
