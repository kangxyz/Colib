/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.AcyclicSubcategory
public import Colib.KTheory.Waldhausen.Functoriality
public import Colib.KTheory.Waldhausen.ZeroFunctor
public import Colib.Topology.HomotopyFiber.Basic

/-! # The original acyclic-to-homotopy-fiber comparison

The path coordinate is the reversed actual weak-natural-transformation
homotopy from the zero functor to the acyclic inclusion. The map lies over the
original inclusion, preserves the original chosen zero, and induces the
original canonical K-map factorization. No fiber equivalence is asserted.


Implementation provenance:
`Quillen/Waldhausen/Fibration/CanonicalFiberMap.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, hypotheses,
chosen zero objects and universe parameters are retained.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open Topology
open scoped Topology
universe u v
namespace CategoryTheory.Waldhausen.Fibration
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V)

/-- The actual zero-to-inclusion transformation; its components are the maps
that define coarse acyclicity. -/
def zeroToAcyclicInclusion : zeroFunctor (C := AcyclicCategory N) N.coarse ⟶ acyclicInclusion N
    where
  app X := N.coarse.isZero.to_ X.obj
  naturality _ _ _ := N.coarse.isZero.eq_of_src _ _

/-- Coarse weakness is precisely the actual object's acyclicity witness. -/
theorem zeroToAcyclicInclusion_weak (X : AcyclicCategory N) :
    N.coarse.weq ((zeroToAcyclicInclusion N).app X) := X.property

/-- The original continuous map changing only the weak-equivalence class. -/
def changeWeakMap : C(V.Delooping, N.coarse.Delooping) := (deloopingMap (changeWeak_exact N)).hom

/-- The original continuous acyclic inclusion. -/
def acyclicInclusionMap : C((acyclicStructure N).Delooping, V.Delooping) :=
  (deloopingMap (acyclicInclusion_exact N)).hom

/-- The composite has its original zero-track nullhomotopy, obtained by reversing
zero-to-inclusion, with no saturation, cylinder, or extension axiom needed. -/
def acyclicNullhomotopy :
    ((changeWeakMap N).comp (acyclicInclusionMap N)).Homotopy
      (ContinuousMap.const _ N.coarse.kBasepoint) := by
  let H := (weakNaturalTransformationRealizationHomotopy (acyclicStructure N) N.coarse
    (zeroFunctor_isExact _ _) (acyclicInclusion_coarse_exact N)
    (zeroToAcyclicInclusion N) (zeroToAcyclicInclusion_weak N)).symm
  have he : (deloopingMap (acyclicInclusion_coarse_exact N)).hom =
      (changeWeakMap N).comp (acyclicInclusionMap N) :=
    congrArg TopCat.Hom.hom
      (deloopingMap_comp_deloopingMap (acyclicInclusion_exact N) (changeWeak_exact N)).symm
  exact {
    toContinuousMap := H.toContinuousMap
    map_zero_left z := (H.map_zero_left z).trans (DFunLike.congr_fun he z)
    map_one_left z := (H.map_one_left z).trans
      (DFunLike.congr_fun (deloopingMap_zeroFunctor (acyclicStructure N) N.coarse) z) }

/-- The nullhomotopy is genuinely based at the actual inherited zero. -/
theorem acyclicNullhomotopy_fixed_zero (t : unitInterval) :
    acyclicNullhomotopy N (t, (acyclicStructure N).kBasepoint) = N.coarse.kBasepoint :=
  weakNaturalTransformationRealizationHomotopy_fixed_zero (acyclicStructure N) N.coarse
    (zeroFunctor_isExact _ _) (acyclicInclusion_coarse_exact N)
    (zeroToAcyclicInclusion N) (zeroToAcyclicInclusion_weak N) rfl
    (by simpa only [acyclicInclusion_zero] using N.coarse_zero.symm) (unitInterval.symm t)

/-- The original change-of-weak-equivalence map retains the chosen zero. -/
theorem changeWeakMap_basepoint : changeWeakMap N V.kBasepoint = N.coarse.kBasepoint :=
  deloopingMap_basepoint_of_zeroEq (changeWeak_exact N) N.zero_eq.symm

/-- The original inclusion retains the chosen zero literally. -/
theorem acyclicInclusionMap_basepoint :
    acyclicInclusionMap N (acyclicStructure N).kBasepoint = V.kBasepoint :=
  deloopingMap_basepoint_of_zeroEq (acyclicInclusion_exact N) rfl

/-- The canonical continuous comparison into the actual homotopy fiber. -/
def canonicalFiberMap : C((acyclicStructure N).Delooping,
    HomotopyFiber (changeWeakMap N) N.coarse.kBasepoint) :=
  HomotopyFiber.lift (changeWeakMap N) N.coarse.kBasepoint
    (acyclicInclusionMap N) (acyclicNullhomotopy N)

/-- Projection is exactly the original acyclic inclusion, without a homotopy replacement. -/
@[simp] theorem canonicalFiberMap_projection :
    (HomotopyFiber.projection (changeWeakMap N) N.coarse.kBasepoint).comp (canonicalFiberMap N) =
      acyclicInclusionMap N := rfl

/-- Its chosen point is the constant-path fiber point over the original fine zero. -/
theorem canonicalFiberMap_basepoint :
    canonicalFiberMap N (acyclicStructure N).kBasepoint =
      HomotopyFiber.basepoint (changeWeakMap N) N.coarse.kBasepoint V.kBasepoint
        (changeWeakMap_basepoint N) := by
  apply Subtype.ext
  apply _root_.Prod.ext
  · exact acyclicInclusionMap_basepoint N
  · apply ContinuousMap.ext
    intro t
    exact acyclicNullhomotopy_fixed_zero N t

/-- The actual canonical comparison on positive homotopy groups, including K₀. -/
def canonicalFiberKMap (n : ℕ) : (acyclicStructure N).K n →*
    HomotopyGroup.Pi (n + 1) (HomotopyFiber (changeWeakMap N) N.coarse.kBasepoint)
      (HomotopyFiber.basepoint (changeWeakMap N) N.coarse.kBasepoint V.kBasepoint
        (changeWeakMap_basepoint N)) :=
  HomotopyGroup.piMap n (canonicalFiberMap N) (canonicalFiberMap_basepoint N)

/-- Its projection is exactly the original canonical acyclic-inclusion K-map. -/
theorem canonicalFiberKMap_projection (n : ℕ) :
    (HomotopyGroup.piMap n (HomotopyFiber.projection (changeWeakMap N) N.coarse.kBasepoint)
      (HomotopyFiber.projection_basepoint _ _ V.kBasepoint (changeWeakMap_basepoint N))).comp
      (canonicalFiberKMap N n) = KMap (acyclicInclusion_exact N) n := by
  rw [KMap_eq_piMap_of_zeroEq (acyclicInclusion_exact N) rfl n]
  exact (HomotopyGroup.mapHom_comp (N := Fin (n + 1))
    (canonicalFiberMap N) (canonicalFiberMap_basepoint N)
    (HomotopyFiber.projection (changeWeakMap N) N.coarse.kBasepoint)
    (HomotopyFiber.projection_basepoint _ _ V.kBasepoint (changeWeakMap_basepoint N))).symm

/-- Consecutive original K-maps compose to the trivial homomorphism.
This is the null-composite half, not a claim of exactness or a fiber theorem. -/
theorem changeWeak_KMap_comp_acyclic (n : ℕ) :
    (KMap (changeWeak_exact N) n).comp (KMap (acyclicInclusion_exact N) n) = 1 := by
  rw [KMap_comp_KMap]
  have h := KMap_eq_of_weakNatTrans (zeroFunctor_isExact (acyclicStructure N) N.coarse)
    (acyclicInclusion_coarse_exact N) (zeroToAcyclicInclusion N)
    (zeroToAcyclicInclusion_weak N) n
  rw [KMap_zeroFunctor] at h
  exact h.symm

end CategoryTheory.Waldhausen.Fibration


namespace CategoryTheory.Waldhausen.Fibration

attribute [colib_tag "COL-0252",
  colib_ref "Waldhausen1985" "Section 1.6, Theorem 1.6.4, the acyclic inclusion square"
    "adaptation"
    "Actual based fiber map with the full reversed zero-to-inclusion nullhomotopy"]
  canonicalFiberMap
  canonicalFiberKMap_projection

end CategoryTheory.Waldhausen.Fibration
