/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.MapComposition
public import Colib.Topology.LocalCoefficients.HomotopyInvariance

/-! # Original chain maps with constant integral-module coefficients -/
/-! Implementation source: `Quillen/Topology/LocalCoefficients/ConstantChainMaps.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, basepoints,
coefficients and signs are retained with native Colib dependencies. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u
namespace FundamentalGroupoid.LocalCoefficients
variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Pulling back a constant system is the original constant system. -/
theorem pullback_constant (f : C(X, Y)) (V : ModuleCat.{u} ℤ) :
    pullback f (constant Y V) = constant X V := rfl

/-- Spatial composition for constant coefficients has no unrecorded transport. -/
@[reassoc]
theorem constant_pushforwardChainMap_comp (f : C(X, Y)) (g : C(Y, Z))
    (V : ModuleCat.{u} ℤ) :
    pushforwardChainMap (g.comp f) (constant Z V) =
      pushforwardChainMap f (constant Y V) ≫ pushforwardChainMap g (constant Z V) := by
  rw [pushforwardChainMap_comp]
  have h : (pullbackCompositionIso f g (constant Z V)).hom = 𝟙 (constant X V) := by
    ext x
    rfl
  rw [h]
  change (coefficientChainFunctor X).map (𝟙 _) ≫ _ = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- The actual identity map acts as the identity on constant-coefficient chains. -/
@[simp]
theorem constant_pushforwardChainMap_id (V : ModuleCat.{u} ℤ) :
    pushforwardChainMap (ContinuousMap.id X) (constant X V) =
      𝟙 (singularChainComplex (constant X V)) := by
  rw [pushforwardChainMap_id]
  have h : (pullbackIdentityIso (constant X V)).hom = 𝟙 (constant X V) := by
    ext x
    rfl
  rw [h]
  exact (coefficientChainFunctor X).map_id _

/-- Constant-coefficient homology preserves the original composite map. -/
@[reassoc]
theorem constant_pushforwardHomologyMap_comp (f : C(X, Y)) (g : C(Y, Z))
    (V : ModuleCat.{u} ℤ) (n : ℕ) :
    pushforwardHomologyMap (g.comp f) (constant Z V) n =
      pushforwardHomologyMap f (constant Y V) n ≫
        pushforwardHomologyMap g (constant Z V) n := by
  unfold pushforwardHomologyMap
  rw [constant_pushforwardChainMap_comp, CategoryTheory.Functor.map_comp]

/-- The original identity map acts identically on constant-coefficient homology. -/
@[simp]
theorem constant_pushforwardHomologyMap_id (V : ModuleCat.{u} ℤ) (n : ℕ) :
    pushforwardHomologyMap (ContinuousMap.id X) (constant X V) n =
      𝟙 (homology (constant X V) n) := by
  unfold pushforwardHomologyMap
  rw [constant_pushforwardChainMap_id]
  exact (HomologicalComplex.homologyFunctor _ _ n).map_id _

end FundamentalGroupoid.LocalCoefficients
