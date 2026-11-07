/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.StableOmega
public import Colib.KTheory.Waldhausen.Iterated.OmegaSpectrum
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-! # Original Waldhausen K-groups as genuine stable homotopy groups

Every nonnegative stable group of the constructed Omega-spectrum is
the original K-group, including the degree-zero group law. The exact
original K-map is preserved under the explicit chosen-zero equality.
The negative stable groups of this connective spectrum vanish; this
does not construct Bass nonconnective K-theory.
-/
/-! Implementation provenance:
`Quillen/Waldhausen/SConstruction/Iterated/StableHomotopy.lean` at Quillen
commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, complete
based tracks, signed degrees, hypotheses and independent universes are retained.
The small source is the native `WideSubcategory preservesZero` on
`SmallWaldhausenCategory`, with the existing `AsSmall` transport. -/
@[expose] public section


noncomputable section
open Topology SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory
open Topology.LoopPrespectrum
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- The original K-group maps to the actual first stable stage by the displayed structure map. -/
def originalKStableStageEquiv (n : ℕ) :
    Additive (W.K n) ≃+ (stableSystem (originalPrespectrum W) (n : ℤ)).obj 0 :=
  ((W.asSmallKEquiv n).trans
    (structurePiEquiv (originalPrespectrum W) (originalPrespectrum_isOmega W) 1 n)).toAdditive.trans
      (nonnegativeStableStageEquiv (originalPrespectrum W) n)

/-- Every nonnegative actual stable homotopy group is the unchanged original K-group,
including degree zero and its group law. -/
def originalKStableEquiv (n : ℕ) :
    Additive (W.K n) ≃+ stableHomotopyGroup (originalPrespectrum W) (n : ℤ) :=
  (originalKStableStageEquiv W n).trans
    (stableHomotopyStageZeroIso (originalPrespectrum W) (originalPrespectrum_isOmega W) (n :
      ℤ)).symm.addCommGroupIsoToAddEquiv

/-- The comparison is exactly the original first-stage inclusion after the displayed K-stage map. -/
theorem originalKStableEquiv_apply (n : ℕ) (a : Additive (W.K n)) :
    originalKStableEquiv W n a = stableHomotopyι (originalPrespectrum W) (n : ℤ) 0
      (originalKStableStageEquiv W n a) := by
  change (stableHomotopyStageZeroIso (originalPrespectrum W) (originalPrespectrum_isOmega W) (n
    : ℤ)).inv
    (originalKStableStageEquiv W n a) = _
  rw [stableHomotopyStageZeroIso_inv]

end CategoryTheory.Waldhausen.IteratedS

open CategoryTheory
namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory
open Topology.LoopPrespectrum
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- The original constructed Waldhausen Omega-spectrum has zero negative stable groups. -/
theorem originalStableHomotopyGroup_neg_subsingleton (d : ℤ) (hd : d < 0) :
    Subsingleton (stableHomotopyGroup (originalPrespectrum W) d) := by
  apply stableHomotopyGroup_subsingleton_of_neg (originalPrespectrum W)
    (originalPrespectrum_isOmega W)
    (fun n ↦ ?_) d hd
  exact stageSpace_pathConnected n (asSmallCategory W)

end CategoryTheory.Waldhausen.IteratedS

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory
open Topology.LoopPrespectrum
variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
  (W : Structure C) (V : Structure D) {F : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F) (h₀ : F.obj W.zero = V.zero)

/-- The first actual stable stage retains the unchanged original K-map. -/
theorem originalKStableStageEquiv_naturality (n : ℕ) (a : W.K n) :
    originalKStableStageEquiv V n (Additive.ofMul (KMap hF n a)) =
      (stableSystemMap (originalPrespectrumMap W V hF h₀) (n : ℤ)).app 0
        (originalKStableStageEquiv W n (Additive.ofMul a)) := by
  have hs := DFunLike.congr_fun (asSmallKEquiv_naturality_of_zeroEq hF h₀ n) a
  change V.asSmallKEquiv n (KMap hF n a) = KMap hF.asSmall n (W.asSmallKEquiv n a) at hs
  rw [KMap_eq_piMap_of_zeroEq hF.asSmall (congrArg AsSmall.up.obj h₀)] at hs
  change nonnegativeStableStageEquiv (originalPrespectrum V) n
    (Additive.ofMul (structurePiMap (originalPrespectrum V) 1 n
      (V.asSmallKEquiv n (KMap hF n a)))) =
    (stableSystemMap (originalPrespectrumMap W V hF h₀) (n : ℤ)).app 0
      (nonnegativeStableStageEquiv (originalPrespectrum W) n
        (Additive.ofMul (structurePiMap (originalPrespectrum W) 1 n (W.asSmallKEquiv n a))))
  rw [← nonnegativeStableStageEquiv_naturality]
  apply congrArg (nonnegativeStableStageEquiv (originalPrespectrum V) n)
  apply congrArg Additive.ofMul
  change structurePiMap (originalPrespectrum V) 1 n (V.asSmallKEquiv n (KMap hF n a)) =
    HomotopyGroup.piMap (n+1) ((originalPrespectrumMap W V hF h₀).map 2)
      ((originalPrespectrumMap W V hF h₀).map_point 2)
      (structurePiMap (originalPrespectrum W) 1 n (W.asSmallKEquiv n a))
  rw [hs]
  exact congrArg (fun h ↦ h (W.asSmallKEquiv n a))
    (structurePiMap_naturality (originalPrespectrumMap W V hF h₀) 1 n)

/-- The actual stable map is exactly the unchanged original K-map under the constructed
equivalence. -/
theorem originalKStableEquiv_naturality (n : ℕ) (a : W.K n) :
    originalKStableEquiv V n (Additive.ofMul (KMap hF n a)) =
      (stableHomotopyFunctor (n : ℤ)).map (originalPrespectrumMap W V hF h₀)
        (originalKStableEquiv W n (Additive.ofMul a)) := by
  rw [originalKStableEquiv_apply, originalKStableEquiv_apply,
    originalKStableStageEquiv_naturality W V hF h₀]
  exact (ConcreteCategory.congr_hom
    (stableHomotopyι_naturality (originalPrespectrumMap W V hF h₀) (n : ℤ) 0)
    (originalKStableStageEquiv W n (Additive.ofMul a))).symm

end CategoryTheory.Waldhausen.IteratedS

attribute [colib_tag "COL-0283",
  colib_ref "ThomasonTrobaugh1990" "Sections 1.5.3-1.5.4, pp. 260-261" "background"
    "The original nonnegative K-groups identify with the actual connective stable groups"]
  CategoryTheory.Waldhausen.IteratedS.originalKStableEquiv

attribute [colib_tag "COL-0283"]
  CategoryTheory.Waldhausen.IteratedS.originalStableHomotopyGroup_neg_subsingleton
