/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Quillen.Automorphism.Universal
public import Colib.RingTheory.KTheory.Quillen.ProjectiveCompletionAutomorphismCones
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.Reversal

/-!
Implementation provenance: `Quillen/KTheory/Plus/ProjectiveCompletionAutomorphismHomotopy.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, tracks,
hypotheses, and signs are retained under native mathematical ownership.

# The original four-arm return family and the Q-cone loop

All identity-quotient and raised-quotient isomorphisms remain explicit.
Composition triangles, the original associator and a common-tail cancellation
give a genuine whole-source homotopy to the full-first Q-cone family. The
native finite-stage source contraction consumes this comparison.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
open Topology HomotopyGroup
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped Topology unitInterval

namespace CategoryTheory.ExactCategory.Automorphism
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- The actual full contraction arm, preceded by the canonical identity-quotient inverse. -/
def identityRaiseCone : (Functor.const (Core C)).obj E.qZero ⟶
    raisedIdentityFunctor E ⋙ E.extensionProjection :=
  E.identityExtensionProjectionIsoZero.inv ≫
    Functor.whiskerRight
      (Functor.whiskerLeft E.identityExtensionFunctor
        (Subdivision.identityToInitialRaise E.inflationZeroIsInitial)) E.extensionProjection

/-- The actual zero contraction arm, preceded by the canonical zero-quotient inverse. -/
def zeroRaiseCone : (Functor.const (Core C)).obj E.qZero ⟶
    raisedIdentityFunctor E ⋙ E.extensionProjection :=
  (constantIdentityProjectionIso E).inv ≫
    Functor.whiskerRight
      (Functor.whiskerLeft E.identityExtensionFunctor
        (Subdivision.constantToInitialRaise E.inflationZeroIsInitial)) E.extensionProjection

/-- The full-first loop of the original corrected contraction cones. -/
def originalContractionConeLoop :
    C(ClassifyingSpace (Core C), Path E.kBasepoint E.kBasepoint) :=
  ConePair.naturalPair (identityRaiseCone E) (zeroRaiseCone E)

/-- The canonical raised-quotient endpoint identifies the first cone with the full Q-cone. -/
theorem identityRaiseCone_normalize :
    identityRaiseCone E ≫ (raisedProjectionIso E).hom = fullCone E := by
  change (_ ≫ _) ≫ _ = _
  rw [Category.assoc]
  exact normalizedIdentityRaiseCone_eq E

/-- The same canonical endpoint identifies the second cone with the zero Q-cone. -/
theorem zeroRaiseCone_normalize :
    zeroRaiseCone E ≫ (raisedProjectionIso E).hom = zeroCone E := by
  change (_ ≫ _) ≫ _ = _
  rw [Category.assoc]
  exact normalizedZeroRaiseCone_eq E

/-- Composition triangles and common-tail cancellation identify the original full-first loop
family. -/
def originalContractionConeLoopHomotopy :
    (originalContractionConeLoop E).Homotopy (loopReversal.comp (universalCoreLoopMap E)) := by
  have H := ConePair.naturalPairSuffixHomotopy
    (identityRaiseCone E) (zeroRaiseCone E) (raisedProjectionIso E).hom
  rw [identityRaiseCone_normalize, zeroRaiseCone_normalize] at H
  refine H.symm.cast rfl ?_
  ext z t
  change ((ConePair.realizedCone (fullCone E)).evalAt z).trans
      ((ConePair.realizedCone (zeroCone E)).evalAt z).symm t =
    (((ConePair.realizedCone (zeroCone E)).evalAt z).trans
      ((ConePair.realizedCone (fullCone E)).evalAt z).symm).symm t
  rw [Path.trans_symm, Path.symm_symm]

end CategoryTheory.ExactCategory.Automorphism

namespace CategoryTheory.ExactCategory.Automorphism
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- Universal realization of the projected identity-to-raise arm. -/
def identityArmHomotopy := classifyingSpaceUniversalHomotopy
  (Functor.whiskerRight (Functor.whiskerLeft E.identityExtensionFunctor
    (Subdivision.identityToInitialRaise E.inflationZeroIsInitial)) E.extensionProjection)

/-- Universal realization of the projected zero-to-raise arm. -/
def zeroArmHomotopy := classifyingSpaceUniversalHomotopy
  (Functor.whiskerRight (Functor.whiskerLeft E.identityExtensionFunctor
    (Subdivision.constantToInitialRaise E.inflationZeroIsInitial)) E.extensionProjection)

/-- The original inverse identity-quotient isomorphism as a whole-source path family. -/
def inverseQuotientHomotopy := ConePair.realizedCone E.identityExtensionProjectionIsoZero.inv

/-- The original inverse zero-quotient isomorphism as a whole-source path family. -/
def constantInverseQuotientHomotopy :=
  ConePair.realizedCone (constantIdentityProjectionIso E).inv

/-- The original four-arm return path, with its actual order and parentheses. -/
def coreReturnHomotopy :=
  ((inverseQuotientHomotopy E).trans
    ((identityArmHomotopy E).trans (zeroArmHomotopy E).symm)).trans
      (constantInverseQuotientHomotopy E).symm

/-- The actual loop-valued four-arm return family. -/
def coreReturnLoopMap := ConePair.closedLoopMap (coreReturnHomotopy E)

/-- The original associators and composition triangles compare the four-arm and two-cone
families. -/
def coreReturnLoopConesHomotopy :
    (coreReturnLoopMap E).Homotopy (originalContractionConeLoop E) := by
  let A := inverseQuotientHomotopy E
  let a := identityArmHomotopy E
  let B := constantInverseQuotientHomotopy E
  let b := zeroArmHomotopy E
  have J₁ : (coreReturnLoopMap E).Homotopy
      (ConePair.loopMap ((A.trans a).trans b.symm) B) :=
    ConePair.relativeLoopHomotopy (A.trans (a.trans b.symm)) ((A.trans a).trans b.symm) B B
      (homotopyAssociator A a b.symm).symm (ContinuousMap.HomotopyRel.refl _ _)
  have J₂ : (ConePair.loopMap ((A.trans a).trans b.symm) B).Homotopy
      (ConePair.loopMap (A.trans a) (B.trans b)) := by
    have h := ConePair.closedRelativeHomotopy
      (((A.trans a).trans b.symm).trans B.symm)
      ((A.trans a).trans (b.symm.trans B.symm))
      (homotopyAssociator (A.trans a) b.symm B.symm)
    refine h.cast rfl ?_
    ext z t
    change (((A.trans a).trans (b.symm.trans B.symm)).evalAt z) t =
      (((A.trans a).evalAt z).trans ((B.trans b).evalAt z).symm) t
    rw [← ContinuousMap.Homotopy.symm_trans]
    rfl
  have J₃ : (originalContractionConeLoop E).Homotopy
      (ConePair.loopMap (A.trans a) (B.trans b)) :=
    ConePair.relativeLoopHomotopy
      (ConePair.realizedCone (identityRaiseCone E)) (A.trans a)
      (ConePair.realizedCone (zeroRaiseCone E)) (B.trans b)
      (TheoremB.universalCompositionHomotopy E.identityExtensionProjectionIsoZero.inv
        (Functor.whiskerRight (Functor.whiskerLeft E.identityExtensionFunctor
          (Subdivision.identityToInitialRaise E.inflationZeroIsInitial)) E.extensionProjection))
      (TheoremB.universalCompositionHomotopy (constantIdentityProjectionIso E).inv
        (Functor.whiskerRight (Functor.whiskerLeft E.identityExtensionFunctor
          (Subdivision.constantToInitialRaise E.inflationZeroIsInitial)) E.extensionProjection))
  exact J₁.trans (J₂.trans J₃.symm)

/-- The actual return family is homotopic to one reversal of the zero-first universal core map. -/
def coreReturnLoopPositiveHomotopy :
    (coreReturnLoopMap E).Homotopy (loopReversal.comp (universalCoreLoopMap E)) :=
  (coreReturnLoopConesHomotopy E).trans (originalContractionConeLoopHomotopy E)

end CategoryTheory.ExactCategory.Automorphism
