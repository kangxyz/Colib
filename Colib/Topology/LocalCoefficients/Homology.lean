/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.Functoriality
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
Extracted from `Quillen/Topology/LocalCoefficients/Homology.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Definitions and proofs use the native
fundamental groupoid, simplicial modules, and Mathlib chain and homology functors.

# Homology with local coefficients

Homology is taken from the actual twisted singular chain complex. Maps come
from the previously constructed chain maps, and coefficient isomorphisms are
retained explicitly. These interfaces do not assume homotopy invariance or
acyclicity of any map.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace FundamentalGroupoid.LocalCoefficients

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The actual homology module of twisted singular chains. -/
def homology (A : System.{u, u} X) (n : ℕ) : ModuleCat.{u} ℤ :=
  (singularChainComplex A).homology n

/-- Homology is functorial in the local coefficient system. -/
def coefficientHomologyFunctor (X : Type u) [TopologicalSpace X] (n : ℕ) :
    System.{u, u} X ⥤ ModuleCat.{u} ℤ :=
  coefficientChainFunctor X ⋙ HomologicalComplex.homologyFunctor _ _ n

/-- The homology map associated to a coefficient morphism. -/
def coefficientHomologyMap {A B : System.{u, u} X} (η : A ⟶ B) (n : ℕ) :
    homology A n ⟶ homology B n :=
  (coefficientHomologyFunctor X n).map η

@[simp]
theorem coefficientHomologyMap_id (A : System.{u, u} X) (n : ℕ) :
    coefficientHomologyMap (𝟙 A) n = 𝟙 (homology A n) :=
  (coefficientHomologyFunctor X n).map_id A

@[reassoc]
theorem coefficientHomologyMap_comp {A B C : System.{u, u} X}
    (η : A ⟶ B) (θ : B ⟶ C) (n : ℕ) :
    coefficientHomologyMap (η ≫ θ) n =
      coefficientHomologyMap η n ≫ coefficientHomologyMap θ n :=
  (coefficientHomologyFunctor X n).map_comp η θ

/-- Isomorphic local systems give the specified homology isomorphism. -/
def coefficientHomologyIso {A B : System.{u, u} X} (e : A ≅ B) (n : ℕ) :
    homology A n ≅ homology B n :=
  (coefficientHomologyFunctor X n).mapIso e

/-- The homology map uses target coefficients pulled back along the original map. -/
def pushforwardHomologyMap (f : C(X, Y)) (A : System.{u, u} Y) (n : ℕ) :
    homology (pullback f A) n ⟶ homology A n :=
  (HomologicalComplex.homologyFunctor _ _ n).map (pushforwardChainMap f A)

/-- Coefficient naturality retains the actual spatial homology map. -/
@[reassoc]
theorem pushforwardHomologyMap_coefficient_naturality (f : C(X, Y))
    {A B : System.{u, u} Y} (η : A ⟶ B) (n : ℕ) :
    coefficientHomologyMap (pullbackMap f η) n ≫ pushforwardHomologyMap f B n =
      pushforwardHomologyMap f A n ≫ coefficientHomologyMap η n := by
  change (HomologicalComplex.homologyFunctor _ _ n).map
      (coefficientChainMap (pullbackMap f η)) ≫ _ =
    _ ≫ (HomologicalComplex.homologyFunctor _ _ n).map (coefficientChainMap η)
  rw [pushforwardHomologyMap, pushforwardHomologyMap, ← Functor.map_comp,
    ← Functor.map_comp, pushforwardChainMap_coefficient_naturality]

/-- Changing the target local system by a specified isomorphism conjugates
its actual induced homology map. -/
theorem pushforwardHomologyMap_coefficient_iso (f : C(X, Y))
    {A B : System.{u, u} Y} (e : A ≅ B) (n : ℕ) :
    pushforwardHomologyMap f B n =
      coefficientHomologyMap (pullbackMap f e.inv) n ≫
        pushforwardHomologyMap f A n ≫ coefficientHomologyMap e.hom n := by
  rw [← pushforwardHomologyMap_coefficient_naturality, ← Category.assoc,
    ← coefficientHomologyMap_comp]
  have h : pullbackMap f e.inv ≫ pullbackMap f e.hom = 𝟙 (pullback f B) := by
    apply NatTrans.ext
    funext x
    exact congrArg (fun η => η.app ((FundamentalGroupoid.map f).obj x)) e.inv_hom_id
  rw [h, coefficientHomologyMap_id, Category.id_comp]

/-- A specified homotopy supplies the coefficient conversion on source homology.
Equality of the endpoint maps requires a separate chain-homotopy proof. -/
def homotopyPullbackHomologyIso {f g : C(X, Y)} (H : f.Homotopy g)
    (A : System.{u, u} Y) (n : ℕ) :
    homology (pullback f A) n ≅ homology (pullback g A) n :=
  coefficientHomologyIso (homotopyPullbackIso H A) n

/-- Constant local coefficients recover mathlib's original singular homology. -/
def constantHomologyIso (V : ModuleCat.{u} ℤ) (n : ℕ) :
    homology (constant X V) n ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj V).obj
        (TopCat.of X) :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (constantChainComplexIso V)

end FundamentalGroupoid.LocalCoefficients
