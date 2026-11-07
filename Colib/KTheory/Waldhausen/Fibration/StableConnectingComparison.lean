/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Waldhausen.Fibration.LevelOneConnectingComparison
public import Colib.Topology.Prespectrum.FiberConnectingLevelOne
public import Colib.Topology.Prespectrum.FiberLiftConnecting
public import Colib.KTheory.Waldhausen.Additivity.GroupFormula

/-!
# The signed stable comparison of the original Waldhausen connecting map

The original K-group equivalence uses exactly one structure map from level one.
The resulting comparison with the prescribed stable fiber boundary has a minus sign.
The canonical fiber lift retains the original whole acyclic nullhomotopy.
-/
/-! Implementation provenance:
`Quillen/Waldhausen/Fibration/StableConnectingComparison.lean` at Quillen
commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, complete
based tracks, signed degrees, hypotheses and independent universes are retained.
The small source is the native `WideSubcategory preservesZero` on
`SmallWaldhausenCategory`, with the existing `AsSmall` transport. -/
@[expose] public section
noncomputable section
open Topology SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology
universe u v
namespace CategoryTheory.Waldhausen.Fibration
open IteratedS LoopPrespectrum
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V)

/-- The unchanged original K-equivalence preserves the actual fiber boundary with a minus sign. -/
theorem originalKStableEquiv_connecting_sign
    (h : IsWeakHomotopyEquivalence (canonicalFiberMap N)) (n : ℕ)
    (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1) (a : N.coarse.K (n + 1)) :
    stableFiberConnecting (changeWeakPrespectrumMap N) (n : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup (originalPrespectrum N.coarse)) κ)
          (originalKStableEquiv N.coarse (n + 1) (Additive.ofMul a))) =
      -((stableHomotopyFunctor (n : ℤ)).map (canonicalFiberPrespectrumMap N)
        (originalKStableEquiv (acyclicStructure N) n
          (Additive.ofMul (changeWeakConnectingHom N h n a)))) := by
  have hF := originalPrespectrum_isOmega N.coarse
  have hA := originalPrespectrum_isOmega (acyclicStructure N)
  have hFib := homotopyFiber_isOmega (changeWeakPrespectrumMap N)
    (originalPrespectrum_isOmega V) hF
  have hs := stableFiberConnecting_levelOneStableEquiv_sign
    (changeWeakPrespectrumMap N) hF hFib n κ (N.coarse.asSmallKEquiv (n + 1) a)
  have hδ := canonicalFiberPrespectrumMap_levelOne_connecting N h n a
  have hn := levelOneStableEquiv_naturality hA hFib (canonicalFiberPrespectrumMap N) n
    ((acyclicStructure N).asSmallKEquiv n (changeWeakConnectingHom N h n a))
  change stableFiberConnecting (changeWeakPrespectrumMap N) (n : ℤ)
      (eqToHom (congrArg (stableHomotopyGroup (originalPrespectrum N.coarse)) κ)
        (levelOneStableEquiv (originalPrespectrum N.coarse) hF (n + 1)
          (Additive.ofMul (N.coarse.asSmallKEquiv (n + 1) a)))) =
    -((stableHomotopyFunctor (n : ℤ)).map (canonicalFiberPrespectrumMap N)
      (levelOneStableEquiv (originalPrespectrum (acyclicStructure N)) hA n
        (Additive.ofMul ((acyclicStructure N).asSmallKEquiv n
          (changeWeakConnectingHom N h n a)))))
  exact hs.trans ((congrArg
    (fun b ↦ -(levelOneStableEquiv (homotopyFiber (changeWeakPrespectrumMap N))
      hFib n (Additive.ofMul b))) hδ.symm).trans (congrArg Neg.neg hn))

/-- The original nonnegative fiber equivalence at the literal specified-lift endpoint. -/
theorem acyclicPrespectrumFiberLift_nonneg_isIso
    (h : IsWeakHomotopyEquivalence (canonicalFiberMap N)) (n : ℕ) :
    IsIso ((stableHomotopyFunctor (n : ℤ)).map
      (homotopyFiberLift (changeWeakPrespectrumMap N) (acyclicInclusionPrespectrumMap N)
        (acyclicPrespectrumNullhomotopy N))) :=
  canonicalFiberPrespectrumMap_nonneg_isIso N h n

/-- The same minus sign holds for the intrinsic boundary of the original specified fiber lift. -/
theorem originalKStableEquiv_liftConnecting_sign
    (h : IsWeakHomotopyEquivalence (canonicalFiberMap N)) (n : ℕ)
    (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1) (a : N.coarse.K (n + 1)) :
    let := acyclicPrespectrumFiberLift_nonneg_isIso N h n
    stableFiberLiftConnecting (acyclicInclusionPrespectrumMap N) (changeWeakPrespectrumMap N)
        (acyclicPrespectrumNullhomotopy N) (n : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup (originalPrespectrum N.coarse)) κ)
          (originalKStableEquiv N.coarse (n + 1) (Additive.ofMul a))) =
      -(originalKStableEquiv (acyclicStructure N) n
        (Additive.ofMul (changeWeakConnectingHom N h n a))) := by
  let := acyclicPrespectrumFiberLift_nonneg_isIso N h n
  let := canonicalFiberPrespectrumMap_nonneg_isIso N h n
  apply (ConcreteCategory.bijective_of_isIso
    ((stableHomotopyFunctor (n : ℤ)).map (canonicalFiberPrespectrumMap N))).injective
  have hc := ConcreteCategory.congr_hom
    (stableFiberLiftConnecting_comp_lift (acyclicInclusionPrespectrumMap N)
      (changeWeakPrespectrumMap N) (acyclicPrespectrumNullhomotopy N) (n : ℤ))
    (eqToHom (congrArg (stableHomotopyGroup (originalPrespectrum N.coarse)) κ)
      (originalKStableEquiv N.coarse (n + 1) (Additive.ofMul a)))
  exact hc.trans ((originalKStableEquiv_connecting_sign N h n κ a).trans (map_neg _ _).symm)

attribute [local instance] Additivity.KCommGroup

/-- The full original group homomorphism square retains its actual degree cast and sign. -/
theorem originalKStableEquiv_connecting_sign_hom
    (h : IsWeakHomotopyEquivalence (canonicalFiberMap N)) (n : ℕ)
    (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1) :
    AddCommGrpCat.ofHom (originalKStableEquiv N.coarse (n + 1)).toAddMonoidHom ≫
        eqToHom (congrArg (stableHomotopyGroup (originalPrespectrum N.coarse)) κ) ≫
        stableFiberConnecting (changeWeakPrespectrumMap N) (n : ℤ) =
      -(AddCommGrpCat.ofHom (changeWeakConnectingHom N h n).toAdditive ≫
        AddCommGrpCat.ofHom (originalKStableEquiv (acyclicStructure N) n).toAddMonoidHom ≫
        (stableHomotopyFunctor (n : ℤ)).map (canonicalFiberPrespectrumMap N)) := by
  ext a
  exact originalKStableEquiv_connecting_sign N h n κ a.toMul

/-- The original stable lift boundary square, with the canonical lift inverse unchanged. -/
theorem originalKStableEquiv_liftConnecting_sign_hom
    (h : IsWeakHomotopyEquivalence (canonicalFiberMap N)) (n : ℕ)
    (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1) :
    let := acyclicPrespectrumFiberLift_nonneg_isIso N h n
    AddCommGrpCat.ofHom (originalKStableEquiv N.coarse (n + 1)).toAddMonoidHom ≫
        eqToHom (congrArg (stableHomotopyGroup (originalPrespectrum N.coarse)) κ) ≫
        stableFiberLiftConnecting (acyclicInclusionPrespectrumMap N)
          (changeWeakPrespectrumMap N) (acyclicPrespectrumNullhomotopy N) (n : ℤ) =
      -(AddCommGrpCat.ofHom (changeWeakConnectingHom N h n).toAdditive ≫
        AddCommGrpCat.ofHom (originalKStableEquiv (acyclicStructure N) n).toAddMonoidHom) := by
  let := acyclicPrespectrumFiberLift_nonneg_isIso N h n
  ext a
  exact originalKStableEquiv_liftConnecting_sign N h n κ a.toMul

end CategoryTheory.Waldhausen.Fibration

attribute [colib_tag "COL-0284"]
  CategoryTheory.Waldhausen.Fibration.originalKStableEquiv_connecting_sign
  CategoryTheory.Waldhausen.Fibration.originalKStableEquiv_liftConnecting_sign
