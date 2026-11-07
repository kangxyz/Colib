/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.RelativeCoefficients
public import Colib.Topology.LocalCoefficients.RelativeFunctoriality
public import Colib.Topology.LocalCoefficients.MapComposition

/-!
Adapted from `Quillen/Topology/LocalCoefficients/RelativeComposition.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual maps and pullbacks.


# Composition of actual relative twisted spatial maps

Naturality, identity, and composition of the original relative pushforward chain
maps follow from the corresponding actual absolute maps by cancellation of the
cokernel projections. Identity and composition explicitly retain their required
pullback coefficient isomorphisms; no pair-level naturality or homotopy is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits

universe u

namespace FundamentalGroupoid.LocalCoefficients

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The original relative spatial map is natural in the actual coefficient system. -/
@[reassoc]
theorem relativePushforwardChainMap_coefficient_naturality (f : C(X, Y))
    (U : Set X) (V : Set Y) (h : Set.MapsTo f U V) {A B : System.{u, u} Y}
    (η : A ⟶ B) :
    relativeCoefficientChainMap U (pullbackMap f η) ≫
        relativePushforwardChainMap f U V h B =
      relativePushforwardChainMap f U V h A ≫ relativeCoefficientChainMap V η := by
  apply (cancel_epi
    (cokernel.π (pushforwardChainMap (subspaceInclusion U) (pullback f A)))).mp
  dsimp only [relativeSingularChainComplex]
  rw [relativeCoefficientChainMap_quotient_assoc, relativePushforwardChainMap_quotient]
  conv_rhs =>
    rw [← Category.assoc, relativePushforwardChainMap_quotient, Category.assoc,
      relativeCoefficientChainMap_quotient]
  rw [← Category.assoc, pushforwardChainMap_coefficient_naturality, Category.assoc]

/-- The identity spatial map on actual quotients retains the identity pullback comparison. -/
theorem relativePushforwardChainMap_id (U : Set X) (A : System.{u, u} X) :
    relativePushforwardChainMap (ContinuousMap.id X) U U (fun _ hx ↦ hx) A =
      relativeCoefficientChainMap U (pullbackIdentityIso A).hom := by
  apply (cancel_epi (cokernel.π
    (pushforwardChainMap (subspaceInclusion U) (pullback (ContinuousMap.id X) A)))).mp
  dsimp only [relativeSingularChainComplex]
  rw [relativePushforwardChainMap_quotient, relativeCoefficientChainMap_quotient,
    pushforwardChainMap_id]

/-- Composition of the original relative spatial maps, with the mandatory
pullback-composition coefficient conversion kept in the formula. -/
@[reassoc]
theorem relativePushforwardChainMap_comp (f : C(X, Y)) (g : C(Y, Z))
    (U : Set X) (V : Set Y) (W : Set Z) (hf : Set.MapsTo f U V)
    (hg : Set.MapsTo g V W) (A : System.{u, u} Z) :
    relativePushforwardChainMap (g.comp f) U W (fun _ hx ↦ hg (hf hx)) A =
      relativeCoefficientChainMap U (pullbackCompositionIso f g A).hom ≫
        relativePushforwardChainMap f U V hf (pullback g A) ≫
          relativePushforwardChainMap g V W hg A := by
  apply (cancel_epi (cokernel.π
    (pushforwardChainMap (subspaceInclusion U) (pullback (g.comp f) A)))).mp
  dsimp only [relativeSingularChainComplex]
  rw [relativePushforwardChainMap_quotient, relativeCoefficientChainMap_quotient_assoc]
  conv_rhs =>
    arg 2
    rw [← Category.assoc, relativePushforwardChainMap_quotient, Category.assoc,
      relativePushforwardChainMap_quotient]
  rw [pushforwardChainMap_comp]
  simp only [Category.assoc]

end FundamentalGroupoid.LocalCoefficients
