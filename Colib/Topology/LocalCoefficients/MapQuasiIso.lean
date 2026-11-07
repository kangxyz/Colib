/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.MapComposition
public import Colib.Topology.LocalCoefficients.Homology
public import Mathlib.Algebra.Homology.QuasiIso

/-!
Adapted from the same-named Quillen source at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using the actual native chain
and homology maps with their coefficient identifications.
 # Composition of original twisted spatial quasi-isomorphisms -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace FundamentalGroupoid.LocalCoefficients
variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Composition retains the original spatial map and the mandatory pullback coefficient iso. -/
theorem pushforwardChainMap_quasiIso_comp (f : C(X, Y)) (g : C(Y, Z))
    (A : System.{u, u} Z) (hf : QuasiIso (pushforwardChainMap f (pullback g A)))
    (hg : QuasiIso (pushforwardChainMap g A)) :
    QuasiIso (pushforwardChainMap (g.comp f) A) := by
  rw [pushforwardChainMap_comp]
  change QuasiIso ((coefficientChainIso (pullbackCompositionIso f g A)).hom ≫
    pushforwardChainMap f (pullback g A) ≫ pushforwardChainMap g A)
  infer_instance

end FundamentalGroupoid.LocalCoefficients
