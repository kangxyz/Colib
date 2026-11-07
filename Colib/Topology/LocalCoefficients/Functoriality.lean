/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.Chains

/-!
Extracted from `Quillen/Topology/LocalCoefficients/Functoriality.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Definitions and proofs use the native
fundamental groupoid, simplicial modules, and Mathlib chain and homology functors.

# Functoriality of local-coefficient singular chains

Natural transformations of coefficient systems and continuous maps of spaces
induce actual maps of the singular simplicial modules. The alternating-face
functor then supplies chain maps; no homology-map assumptions are used.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace FundamentalGroupoid.LocalCoefficients

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Apply a map of local systems to every actual simplex coefficient. -/
def coefficientModuleMap {A B : System.{u, u} X} (η : A ⟶ B) (n : SimplexCategory) :
    chainModule A n ⟶ chainModule B n :=
  Sigma.desc fun σ ↦ η.app (FundamentalGroupoid.mk (σ (stdSimplex.vertex 0))) ≫
    chainInclusion B σ

@[reassoc (attr := simp)]
theorem chainInclusion_coefficientModuleMap {A B : System.{u, u} X} (η : A ⟶ B)
    {n : SimplexCategory} (σ : SingularSimplex X n) :
    chainInclusion A σ ≫ coefficientModuleMap η n =
      η.app (FundamentalGroupoid.mk (σ (stdSimplex.vertex 0))) ≫ chainInclusion B σ :=
  Sigma.ι_desc _ _

/-- Coefficient morphisms commute with the transported simplicial restrictions. -/
@[reassoc]
theorem restrictionTransport_naturality {A B : System.{u, u} X} (η : A ⟶ B)
    {m n : SimplexCategory} (σ : SingularSimplex X n) (α : m ⟶ n) :
    restrictionTransport A σ α ≫
        η.app (FundamentalGroupoid.mk (restrictSimplex σ α (stdSimplex.vertex 0))) =
      η.app (FundamentalGroupoid.mk (σ (stdSimplex.vertex 0))) ≫
        restrictionTransport B σ α :=
  transport_naturality η _

/-- A coefficient natural transformation gives a genuine simplicial map. -/
def coefficientSimplicialMap {A B : System.{u, u} X} (η : A ⟶ B) :
    simplicialModule A ⟶ simplicialModule B where
  app n := coefficientModuleMap η n.unop
  naturality n m α := by
    apply Sigma.hom_ext
    intro σ
    change chainInclusion A σ ≫ (chainMap A α.unop ≫ coefficientModuleMap η m.unop) =
      chainInclusion A σ ≫ (coefficientModuleMap η n.unop ≫ chainMap B α.unop)
    simp only [chainInclusion_chainMap_assoc, chainInclusion_coefficientModuleMap,
      chainInclusion_coefficientModuleMap_assoc, chainInclusion_chainMap]
    rw [← Category.assoc, restrictionTransport_naturality, Category.assoc]

/-- The chain map associated to a morphism of coefficient systems. -/
def coefficientChainMap {A B : System.{u, u} X} (η : A ⟶ B) :
    singularChainComplex A ⟶ singularChainComplex B :=
  (AlgebraicTopology.alternatingFaceMapComplex _).map (coefficientSimplicialMap η)

@[simp]
theorem coefficientSimplicialMap_id (A : System.{u, u} X) :
    coefficientSimplicialMap (𝟙 A) = 𝟙 (simplicialModule A) := by
  ext n : 1
  apply Sigma.hom_ext
  intro σ
  simp [coefficientSimplicialMap, coefficientModuleMap, chainInclusion, simplicialModule,
    chainModule]

@[reassoc]
theorem coefficientSimplicialMap_comp {A B C : System.{u, u} X}
    (η : A ⟶ B) (θ : B ⟶ C) :
    coefficientSimplicialMap (η ≫ θ) =
      coefficientSimplicialMap η ≫ coefficientSimplicialMap θ := by
  ext n : 1
  apply Sigma.hom_ext
  intro σ
  simp [coefficientSimplicialMap, coefficientModuleMap, chainInclusion, simplicialModule,
    chainModule]

/-- Functorial singular chains in the local coefficient system. -/
def coefficientChainFunctor (X : Type u) [TopologicalSpace X] :
    System.{u, u} X ⥤ ChainComplex (ModuleCat.{u} ℤ) ℕ where
  obj A := singularChainComplex A
  map η := coefficientChainMap η
  map_id A := by simp [coefficientChainMap, singularChainComplex]
  map_comp η θ := by
    simp [coefficientChainMap, coefficientSimplicialMap_comp]

/-- Isomorphic coefficient systems give canonically isomorphic actual chain complexes. -/
def coefficientChainIso {A B : System.{u, u} X} (e : A ≅ B) :
    singularChainComplex A ≅ singularChainComplex B :=
  (coefficientChainFunctor X).mapIso e

/-- A continuous map sends an actual singular simplex to its composite. -/
def pushforwardModuleMap (f : C(X, Y)) (A : System.{u, u} Y) (n : SimplexCategory) :
    chainModule (pullback f A) n ⟶ chainModule A n :=
  Sigma.desc fun σ ↦ chainInclusion A (f.comp σ)

@[reassoc (attr := simp)]
theorem chainInclusion_pushforwardModuleMap (f : C(X, Y)) (A : System.{u, u} Y)
    {n : SimplexCategory} (σ : SingularSimplex X n) :
    chainInclusion (pullback f A) σ ≫ pushforwardModuleMap f A n =
      chainInclusion A (f.comp σ) :=
  Sigma.ι_desc _ _

/-- Pullback coefficients make transport compatible with postcomposition of simplices. -/
theorem restrictionTransport_pushforward (f : C(X, Y)) (A : System.{u, u} Y)
    {m n : SimplexCategory} (σ : SingularSimplex X n) (α : m ⟶ n) :
    restrictionTransport (pullback f A) σ α = restrictionTransport A (f.comp σ) α := rfl

/-- The actual simplicial map on chains induced by a continuous map. -/
def pushforwardSimplicialMap (f : C(X, Y)) (A : System.{u, u} Y) :
    simplicialModule (pullback f A) ⟶ simplicialModule A where
  app n := pushforwardModuleMap f A n.unop
  naturality n m α := by
    apply Sigma.hom_ext
    intro σ
    change chainInclusion (pullback f A) σ ≫
        (chainMap (pullback f A) α.unop ≫ pushforwardModuleMap f A m.unop) =
      chainInclusion (pullback f A) σ ≫ (pushforwardModuleMap f A n.unop ≫ chainMap A α.unop)
    simp only [chainInclusion_chainMap_assoc, chainInclusion_pushforwardModuleMap,
      chainInclusion_pushforwardModuleMap_assoc, chainInclusion_chainMap,
      restrictionTransport_pushforward]
    rfl

/-- The chain map `C_*(X; f* A) → C_*(Y; A)` induced by a continuous map. -/
def pushforwardChainMap (f : C(X, Y)) (A : System.{u, u} Y) :
    singularChainComplex (pullback f A) ⟶ singularChainComplex A :=
  (AlgebraicTopology.alternatingFaceMapComplex _).map (pushforwardSimplicialMap f A)

/-- Pull back an actual coefficient morphism along a continuous map. -/
def pullbackMap (f : C(X, Y)) {A B : System.{u, u} Y} (η : A ⟶ B) :
    pullback f A ⟶ pullback f B :=
  Functor.whiskerLeft (FundamentalGroupoid.map f) η

/-- Spatial functoriality commutes with maps of local coefficient systems. -/
@[reassoc]
theorem pushforwardSimplicialMap_coefficient_naturality (f : C(X, Y))
    {A B : System.{u, u} Y} (η : A ⟶ B) :
    coefficientSimplicialMap (pullbackMap f η) ≫ pushforwardSimplicialMap f B =
      pushforwardSimplicialMap f A ≫ coefficientSimplicialMap η := by
  ext n : 1
  apply Sigma.hom_ext
  intro σ
  simp [coefficientSimplicialMap, pushforwardSimplicialMap, coefficientModuleMap,
    pushforwardModuleMap, chainInclusion, pullbackMap]
  rfl

/-- The corresponding naturality square consists of actual chain maps. -/
@[reassoc]
theorem pushforwardChainMap_coefficient_naturality (f : C(X, Y))
    {A B : System.{u, u} Y} (η : A ⟶ B) :
    coefficientChainMap (pullbackMap f η) ≫ pushforwardChainMap f B =
      pushforwardChainMap f A ≫ coefficientChainMap η := by
  simp only [coefficientChainMap, pushforwardChainMap, ← Functor.map_comp,
    pushforwardSimplicialMap_coefficient_naturality]

/-- A homotopy supplies the actual coefficient conversion needed before its
endpoint chain maps can even be compared. -/
def homotopyPullbackChainIso {f g : C(X, Y)} (H : f.Homotopy g)
    (A : System.{u, u} Y) :
    singularChainComplex (pullback f A) ≅ singularChainComplex (pullback g A) :=
  coefficientChainIso (homotopyPullbackIso H A)

end FundamentalGroupoid.LocalCoefficients
