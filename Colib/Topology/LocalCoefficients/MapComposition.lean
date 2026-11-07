/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.Functoriality

/-!
Adapted from `Quillen/Topology/LocalCoefficients/MapComposition.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using the pinned native singular
simplices, module coproducts, and chain/homology functors.

# Spatial composition with local coefficients

The identity and composition comparisons retain the original pullback systems
and actual chain maps. The coefficient identifications have identity components;
no equality between differently typed chain complexes is silently assumed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory

universe u

namespace FundamentalGroupoid.LocalCoefficients

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Canonical coefficient identification for the identity map. -/
def pullbackIdentityIso (A : System.{u, u} X) : pullback (ContinuousMap.id X) A ≅ A :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro x y p
    obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective p
    simp only [Iso.refl_hom]
    rfl)

/-- Canonical coefficient comparison for composed continuous maps. -/
def pullbackCompositionIso (f : C(X, Y)) (g : C(Y, Z)) (A : System.{u, u} Z) :
    pullback (g.comp f) A ≅ pullback f (pullback g A) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro x y p
    obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective p
    simp only [Iso.refl_hom]
    rfl)

/-- The identity spatial map retains the specified coefficient identification. -/
theorem pushforwardSimplicialMap_id (A : System.{u, u} X) :
    pushforwardSimplicialMap (ContinuousMap.id X) A =
      coefficientSimplicialMap (pullbackIdentityIso A).hom := by
  ext n : 1
  apply Limits.Sigma.hom_ext
  intro σ
  simp [pushforwardSimplicialMap, coefficientSimplicialMap,
    pushforwardModuleMap, coefficientModuleMap, pullbackIdentityIso]
  rfl

/-- Spatial composition retains its original pullback coefficient comparison. -/
theorem pushforwardSimplicialMap_comp (f : C(X, Y)) (g : C(Y, Z)) (A : System.{u, u} Z) :
    pushforwardSimplicialMap (g.comp f) A =
      coefficientSimplicialMap (pullbackCompositionIso f g A).hom ≫
        pushforwardSimplicialMap f (pullback g A) ≫ pushforwardSimplicialMap g A := by
  ext n : 1
  apply Limits.Sigma.hom_ext
  intro σ
  simp [pushforwardSimplicialMap, coefficientSimplicialMap,
    pushforwardModuleMap, coefficientModuleMap, pullbackCompositionIso, chainInclusion]

/-- Identity functoriality on actual local-coefficient chain complexes. -/
theorem pushforwardChainMap_id (A : System.{u, u} X) :
    pushforwardChainMap (ContinuousMap.id X) A =
      coefficientChainMap (pullbackIdentityIso A).hom := by
  rw [pushforwardChainMap, pushforwardSimplicialMap_id, coefficientChainMap]

/-- Composition of actual chain maps, including its coefficient conversion. -/
theorem pushforwardChainMap_comp (f : C(X, Y)) (g : C(Y, Z))
    (A : System.{u, u} Z) :
    pushforwardChainMap (g.comp f) A =
      coefficientChainMap (pullbackCompositionIso f g A).hom ≫
        pushforwardChainMap f (pullback g A) ≫ pushforwardChainMap g A := by
  simp only [pushforwardChainMap, coefficientChainMap, pushforwardSimplicialMap_comp,
    Functor.map_comp]

end FundamentalGroupoid.LocalCoefficients
