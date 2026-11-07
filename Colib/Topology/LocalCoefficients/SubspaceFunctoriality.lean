/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.SubspaceSmallChains
public import Colib.Topology.LocalCoefficients.SmallChainFunctoriality
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
Adapted from `Quillen/Topology/LocalCoefficients/SubspaceFunctoriality.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual maps and pullbacks.

 # The actual subspace spatial map and its small-chain comparison -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits

universe u

namespace FundamentalGroupoid.LocalCoefficients

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) (U : Set X) (V : Set Y) (h : Set.MapsTo f U V)
  (A : System.{u, u} Y)

/-- The actual continuous restriction to a mapped pair of subspaces. -/
def subspaceMap : C(U, V) :=
  ⟨fun x ↦ ⟨f x.val, h x.property⟩, (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The two restrictions of the actual target local system agree on its fibers
and its original path transports. -/
def subspaceMapPullbackIso :
    pullback (subspaceInclusion U) (pullback f A) ≅
      pullback (subspaceMap f U V h) (pullback (subspaceInclusion V) A) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    rintro x y ⟨p⟩
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl)

/-- Spatial functoriality on subspace chains, with its required coefficient conversion. -/
def subspacePushforwardChainMap :
    singularChainComplex (pullback (subspaceInclusion U) (pullback f A)) ⟶
      singularChainComplex (pullback (subspaceInclusion V) A) :=
  (coefficientChainIso (subspaceMapPullbackIso f U V h A)).hom ≫
    pushforwardChainMap (subspaceMap f U V h) (pullback (subspaceInclusion V) A)

/-- The subspace chain map is the original small-chain spatial map under the
proved subspace identifications. -/
@[reassoc]
theorem subspacePushforwardChainMap_smallChainIso :
    subspacePushforwardChainMap f U V h A ≫ (subspaceSmallChainIso V A).hom =
      (subspaceSmallChainIso U (pullback f A)).hom ≫
        smallPushforwardChainMap f (singletonCover U) (singletonCover V) A
          (fun hσ ↦ hσ.map id (fun _ ↦ h)) := by
  ext n : 1
  apply Sigma.hom_ext
  intro σ
  simp [subspacePushforwardChainMap, coefficientChainIso, coefficientChainFunctor,
    coefficientChainMap, coefficientSimplicialMap, coefficientModuleMap,
    subspaceMapPullbackIso, pushforwardChainMap, pushforwardSimplicialMap,
    pushforwardModuleMap, subspaceSmallChainIso, subspaceSmallSimplicialIso,
    subspaceSmallModuleIso, subspaceSmallModuleMap, smallPushforwardChainMap,
    smallPushforwardSimplicialMap, smallPushforwardModuleMap,
    chainInclusion, smallChainInclusion]
  rfl

/-- The subspace and small-chain formulations test the same original map. -/
theorem subspacePushforwardChainMap_quasiIso_iff :
    QuasiIso (subspacePushforwardChainMap f U V h A) ↔
      QuasiIso (smallPushforwardChainMap f (singletonCover U) (singletonCover V) A
        (fun hσ ↦ hσ.map id (fun _ ↦ h))) := by
  rw [← quasiIso_iff_comp_right (subspacePushforwardChainMap f U V h A)
    (subspaceSmallChainIso V A).hom, subspacePushforwardChainMap_smallChainIso,
    quasiIso_iff_comp_left]

end FundamentalGroupoid.LocalCoefficients
