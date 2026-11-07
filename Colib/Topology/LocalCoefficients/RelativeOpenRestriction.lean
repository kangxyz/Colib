/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.OpenExcision
public import Colib.Topology.LocalCoefficients.RelativeComposition

/-!
Adapted from `Quillen/Topology/LocalCoefficients/RelativeOpenRestriction.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual maps and pullbacks.


# Original relative maps compared on excisive open restrictions

The comparison square retains its actual subspace pullback isomorphism. Excision
on the two genuine open covers then detects a quasi-isomorphism of the original
ambient pair map from the corresponding original restricted pair map.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits
universe u
namespace FundamentalGroupoid.LocalCoefficients
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The exact coefficient-corrected square of original relative restriction maps. -/
theorem relativePushforwardChainMap_openRestriction_square (f : C(X, Y))
    (U V : Set X) (U' V' : Set Y) (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V')
    (A : System.{u, u} Y) :
    relativePushforwardChainMap (subspaceInclusion U)
        (intersectionInSubspace U V) V (fun _ hx ↦ hx) (pullback f A) ≫
      relativePushforwardChainMap f V V' hV A =
    relativeCoefficientChainMap (intersectionInSubspace U V)
        (subspaceMapPullbackIso f U U' hU A).hom ≫
      relativePushforwardChainMap (subspaceMap f U U' hU)
        (intersectionInSubspace U V) (intersectionInSubspace U' V')
        (fun _ hx ↦ hV hx) (pullback (subspaceInclusion U') A) ≫
      relativePushforwardChainMap (subspaceInclusion U')
        (intersectionInSubspace U' V') V' (fun _ hx ↦ hx) A := by
  apply (cancel_epi (cokernel.π
    (pushforwardChainMap (subspaceInclusion (intersectionInSubspace U V))
      (pullback (subspaceInclusion U) (pullback f A))))).mp
  simp only [← Category.assoc]
  rw [relativePushforwardChainMap_quotient, relativeCoefficientChainMap_quotient]
  simp only [Category.assoc]
  rw [relativePushforwardChainMap_quotient]
  rw [← Category.assoc
    (cokernel.π (pushforwardChainMap
      (subspaceInclusion (intersectionInSubspace U V))
      (pullback (subspaceMap f U U' hU) (pullback (subspaceInclusion U') A))))
    (relativePushforwardChainMap (subspaceMap f U U' hU)
      (intersectionInSubspace U V) (intersectionInSubspace U' V')
      (fun _ hx ↦ hV hx) (pullback (subspaceInclusion U') A))
    (relativePushforwardChainMap (subspaceInclusion U')
      (intersectionInSubspace U' V') V' (fun _ hx ↦ hx) A),
    relativePushforwardChainMap_quotient, Category.assoc,
    relativePushforwardChainMap_quotient]
  simpa only [relativeSingularChainComplex, subspacePushforwardChainMap, coefficientChainIso,
    Functor.mapIso_hom, coefficientChainFunctor, Category.assoc] using congrArg
      (fun k ↦ k ≫ cokernel.π (pushforwardChainMap (subspaceInclusion V') A))
      (subspacePushforwardChainMap_inclusion f U U' hU A).symm

/-- Actual open excision on both sides detects the original ambient pair comparison. -/
theorem relativePushforwardChainMap_quasiIso_of_openRestriction (f : C(X, Y))
    (U V : Set X) (U' V' : Set Y) (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V')
    (A : System.{u, u} Y) (hoU : IsOpen U) (hoV : IsOpen V) (hc : U ∪ V = Set.univ)
    (hoU' : IsOpen U') (hoV' : IsOpen V') (hc' : U' ∪ V' = Set.univ)
    (hq : QuasiIso (relativePushforwardChainMap (subspaceMap f U U' hU)
      (intersectionInSubspace U V) (intersectionInSubspace U' V')
      (fun _ hx ↦ hV hx) (pullback (subspaceInclusion U') A))) :
    QuasiIso (relativePushforwardChainMap f V V' hV A) := by
  have := relativePushforwardChainMap_openExcision U V (pullback f A) hoU hoV hc
  have := relativePushforwardChainMap_openExcision U' V' A hoU' hoV' hc'
  have : QuasiIso (relativePushforwardChainMap (subspaceInclusion U)
      (intersectionInSubspace U V) V (fun _ hx ↦ hx) (pullback f A) ≫
        relativePushforwardChainMap f V V' hV A) := by
    rw [relativePushforwardChainMap_openRestriction_square f U V U' V' hU hV A]
    infer_instance
  exact quasiIso_of_comp_left
    (relativePushforwardChainMap (subspaceInclusion U) (intersectionInSubspace U V) V
      (fun _ hx ↦ hx) (pullback f A))
    (relativePushforwardChainMap f V V' hV A)

end FundamentalGroupoid.LocalCoefficients
