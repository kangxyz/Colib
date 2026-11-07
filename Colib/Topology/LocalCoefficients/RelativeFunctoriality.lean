/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.SubspaceFunctoriality
public import Colib.Topology.LocalCoefficients.RelativeChains
public import Colib.Topology.LocalCoefficients.RelativeAcyclicity

/-!
Adapted from `Quillen/Topology/LocalCoefficients/RelativeFunctoriality.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual maps and pullbacks.

 # Functoriality of actual relative twisted singular chains -/
@[expose] public section
noncomputable section
open CategoryTheory Limits
universe u
namespace FundamentalGroupoid.LocalCoefficients
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) (U : Set X) (V : Set Y) (h : Set.MapsTo f U V)
  (A : System.{u, u} Y)

/-- The original subspace map commutes with the original spatial chain inclusions. -/
@[reassoc]
theorem subspacePushforwardChainMap_inclusion :
    subspacePushforwardChainMap f U V h A ≫
        pushforwardChainMap (subspaceInclusion V) A =
      pushforwardChainMap (subspaceInclusion U) (pullback f A) ≫
        pushforwardChainMap f A := by
  rw [← subspaceSmallChainIso_hom_inclusion V A,
    ← Category.assoc, subspacePushforwardChainMap_smallChainIso, Category.assoc,
    smallPushforwardChainMap_inclusion, ← Category.assoc,
    subspaceSmallChainIso_hom_inclusion]

/-- The actual map of relative singular complexes induced by a continuous map of pairs. -/
def relativePushforwardChainMap : relativeSingularChainComplex U (pullback f A) ⟶
    relativeSingularChainComplex V A :=
  cokernel.map _ _ (subspacePushforwardChainMap f U V h A) (pushforwardChainMap f A)
    (subspacePushforwardChainMap_inclusion f U V h A).symm

/-- The relative map retains exactly the original absolute spatial chain map. -/
@[reassoc]
theorem relativePushforwardChainMap_quotient :
    cokernel.π (pushforwardChainMap (subspaceInclusion U) (pullback f A)) ≫
        relativePushforwardChainMap f U V h A =
      pushforwardChainMap f A ≫
        cokernel.π (pushforwardChainMap (subspaceInclusion V) A) := by
  exact cokernel.π_desc _ _ _

/-- A quasi-isomorphism on both actual absolute terms induces a quasi-isomorphism
on the original relative map, with the subspace coefficient conversion retained. -/
theorem relativePushforwardChainMap_quasiIso
    (hf : QuasiIso (pushforwardChainMap f A))
    (hsub : QuasiIso (subspacePushforwardChainMap f U V h A)) :
    QuasiIso (relativePushforwardChainMap f U V h A) := by
  let S := ShortComplex.mk (pushforwardChainMap (subspaceInclusion U) (pullback f A))
    (cokernel.π _) (cokernel.condition _)
  let T := ShortComplex.mk (pushforwardChainMap (subspaceInclusion V) A)
    (cokernel.π _) (cokernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  have hT : T.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  let φ : S ⟶ T :=
    { τ₁ := subspacePushforwardChainMap f U V h A
      τ₂ := pushforwardChainMap f A
      τ₃ := relativePushforwardChainMap f U V h A
      comm₁₂ := subspacePushforwardChainMap_inclusion f U V h A
      comm₂₃ := (relativePushforwardChainMap_quotient f U V h A).symm }
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ φ hS hT hsub hf

/-- Genuine homotopy equivalences of the ambient and subspace maps suffice
for the original relative twisted chain map. -/
theorem relativePushforwardChainMap_quasiIso_of_homotopyEquiv
    (e : ContinuousMap.HomotopyEquiv X Y) (he : e.toFun = f)
    (s : ContinuousMap.HomotopyEquiv U V) (hs : s.toFun = subspaceMap f U V h) :
    QuasiIso (relativePushforwardChainMap f U V h A) := by
  apply relativePushforwardChainMap_quasiIso
  · rw [← he]
    exact pushforwardChainMap_quasiIso_of_homotopyEquiv e A
  · have hh := pushforwardChainMap_quasiIso_of_homotopyEquiv s
      (pullback (subspaceInclusion V) A)
    rw [hs] at hh
    unfold subspacePushforwardChainMap
    infer_instance

end FundamentalGroupoid.LocalCoefficients
