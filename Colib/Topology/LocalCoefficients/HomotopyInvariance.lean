/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.Homology
public import Colib.Topology.LocalCoefficients.Homotopy
public import Colib.Topology.LocalCoefficients.MapComposition

/-!
Adapted from `Quillen/Topology/LocalCoefficients/HomotopyInvariance.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using the pinned native singular
simplices, module coproducts, and chain/homology functors.

# Homotopy invariance of actual local-coefficient homology maps

The chain homotopy is built from actual transported prism chains. Applying
homology gives equality only after the specified homotopy's coefficient
conversion. Identity and composition formulas retain their own comparisons.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace FundamentalGroupoid.LocalCoefficients

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Homotopic maps agree on homology after the actual coefficient transport. -/
theorem pushforwardHomologyMap_homotopy {f g : C(X, Y)} (H : f.Homotopy g)
    (A : System.{u, u} Y) (n : ℕ) :
    pushforwardHomologyMap f A n =
      (homotopyPullbackHomologyIso H A n).hom ≫ pushforwardHomologyMap g A n := by
  change (HomologicalComplex.homologyFunctor _ _ n).map (pushforwardChainMap f A) =
    (HomologicalComplex.homologyFunctor _ _ n).map
        (homotopyPullbackChainIso H A).hom ≫
      (HomologicalComplex.homologyFunctor _ _ n).map (pushforwardChainMap g A)
  rw [← Functor.map_comp]
  exact (pushforwardChainHomotopy H A).homologyMap_eq n

/-- Being an isomorphism on a fixed target local system is homotopy invariant. -/
theorem isIso_pushforwardHomologyMap_iff_of_homotopy {f g : C(X, Y)}
    (H : f.Homotopy g) (A : System.{u, u} Y) (n : ℕ) :
    IsIso (pushforwardHomologyMap f A n) ↔ IsIso (pushforwardHomologyMap g A n) := by
  rw [pushforwardHomologyMap_homotopy H A n]
  exact isIso_comp_left_iff _ _

/-- The identity spatial map induces the canonical pullback identification. -/
theorem pushforwardHomologyMap_id (A : System.{u, u} X) (n : ℕ) :
    pushforwardHomologyMap (ContinuousMap.id X) A n =
      coefficientHomologyMap (pullbackIdentityIso A).hom n := by
  change (HomologicalComplex.homologyFunctor _ _ n).map _ =
    (HomologicalComplex.homologyFunctor _ _ n).map _
  rw [pushforwardChainMap_id]
  rfl

/-- Composition of spatial homology maps keeps the pullback coefficient comparison. -/
theorem pushforwardHomologyMap_comp (f : C(X, Y)) (g : C(Y, Z))
    (A : System.{u, u} Z) (n : ℕ) :
    pushforwardHomologyMap (g.comp f) A n =
      coefficientHomologyMap (pullbackCompositionIso f g A).hom n ≫
        pushforwardHomologyMap f (pullback g A) n ≫ pushforwardHomologyMap g A n := by
  change (HomologicalComplex.homologyFunctor _ _ n).map _ =
    (HomologicalComplex.homologyFunctor _ _ n).map _ ≫
      (HomologicalComplex.homologyFunctor _ _ n).map _ ≫
        (HomologicalComplex.homologyFunctor _ _ n).map _
  rw [pushforwardChainMap_comp, Functor.map_comp, Functor.map_comp]
  rfl

end FundamentalGroupoid.LocalCoefficients
