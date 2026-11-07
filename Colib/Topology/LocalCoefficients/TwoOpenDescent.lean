/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.OpenCoverDescent
public import Colib.Topology.LocalCoefficients.SubspaceFunctoriality

/-!
Adapted from `Quillen/Topology/LocalCoefficients/TwoOpenDescent.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps.

# Two-open-set comparison for the original twisted singular map

This statement uses the actual spatial restrictions to the two subspaces and
their intersection. Their coefficients are the actual restricted target
system with its explicit pullback conversion. These three local comparisons
imply the quasi-isomorphism of the original ambient spatial map.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory

universe u

namespace FundamentalGroupoid.LocalCoefficients

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Two compatible subspace maps also give the actual map on their intersection. -/
theorem mapsTo_intersection (f : C(X, Y)) (U V : Set X) (U' V' : Set Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V') :
    Set.MapsTo f (U ∩ V) (U' ∩ V') :=
  fun _ hx ↦ ⟨hU hx.1, hV hx.2⟩

/-- Actual twisted singular homology comparisons glue across two open subsets.
No Hausdorffness, constant coefficients, or fibration conclusion is assumed. -/
theorem pushforwardChainMap_quasiIso_of_two_open_subspaces
    (f : C(X, Y)) (U V : Set X) (U' V' : Set Y) (A : System.{u, u} Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V')
    (openU : IsOpen U) (openV : IsOpen V) (coverX : U ∪ V = Set.univ)
    (openU' : IsOpen U') (openV' : IsOpen V') (coverY : U' ∪ V' = Set.univ)
    (h₁ : QuasiIso (subspacePushforwardChainMap f U U' hU A))
    (h₂ : QuasiIso (subspacePushforwardChainMap f V V' hV A))
    (h₁₂ : QuasiIso (subspacePushforwardChainMap f (U ∩ V) (U' ∩ V')
      (mapsTo_intersection f U V U' V' hU hV) A)) :
    QuasiIso (pushforwardChainMap f A) := by
  refine pushforwardChainMap_quasiIso_of_open_covers f
    (singletonCover U) (singletonCover V) (singletonCover U') (singletonCover V') A
    (fun hσ ↦ hσ.map id (fun _ ↦ hU)) (fun hσ ↦ hσ.map id (fun _ ↦ hV))
    (fun _ ↦ openU) (fun _ ↦ openV) ?_ (fun _ ↦ openU') (fun _ ↦ openV') ?_
    ((subspacePushforwardChainMap_quasiIso_iff f U U' hU A).mp h₁)
    ((subspacePushforwardChainMap_quasiIso_iff f V V' hV A).mp h₂) ?_
  · intro x
    have hx : x ∈ U ∪ V := by rw [coverX]; trivial
    rcases hx with hx | hx
    · exact Or.inl ⟨(), hx⟩
    · exact Or.inr ⟨(), hx⟩
  · intro y
    have hy : y ∈ U' ∪ V' := by rw [coverY]; trivial
    rcases hy with hy | hy
    · exact Or.inl ⟨(), hy⟩
    · exact Or.inr ⟨(), hy⟩
  · apply smallPushforwardChainMap_quasiIso_of_cover_iff f
      (singletonCover (U ∩ V)) (singletonCover (U' ∩ V')) A
      (fun hσ ↦ hσ.map id (fun _ ↦ mapsTo_intersection f U V U' V' hU hV))
      (intersectionCover (singletonCover U) (singletonCover V))
      (intersectionCover (singletonCover U') (singletonCover V'))
      (mapSmallIntersection f (singletonCover U) (singletonCover V)
        (singletonCover U') (singletonCover V')
        (fun hσ ↦ hσ.map id (fun _ ↦ hU)) (fun hσ ↦ hσ.map id (fun _ ↦ hV)))
    · intro n σ
      simp [Set.subset_inter_iff]
    · intro n σ
      simp [Set.subset_inter_iff]
    · exact (subspacePushforwardChainMap_quasiIso_iff f (U ∩ V) (U' ∩ V')
        (mapsTo_intersection f U V U' V' hU hV) A).mp h₁₂

/-- The original spatial homology map is an isomorphism in every degree under
the same actual local-subspace hypotheses. -/
theorem pushforwardHomologyMap_isIso_of_two_open_subspaces
    (f : C(X, Y)) (U V : Set X) (U' V' : Set Y) (A : System.{u, u} Y)
    (hU : Set.MapsTo f U U') (hV : Set.MapsTo f V V')
    (openU : IsOpen U) (openV : IsOpen V) (coverX : U ∪ V = Set.univ)
    (openU' : IsOpen U') (openV' : IsOpen V') (coverY : U' ∪ V' = Set.univ)
    (h₁ : QuasiIso (subspacePushforwardChainMap f U U' hU A))
    (h₂ : QuasiIso (subspacePushforwardChainMap f V V' hV A))
    (h₁₂ : QuasiIso (subspacePushforwardChainMap f (U ∩ V) (U' ∩ V')
      (mapsTo_intersection f U V U' V' hU hV) A)) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (pushforwardChainMap f A) n) := by
  have := pushforwardChainMap_quasiIso_of_two_open_subspaces f U V U' V' A hU hV
    openU openV coverX openU' openV' coverY h₁ h₂ h₁₂
  infer_instance

end FundamentalGroupoid.LocalCoefficients
