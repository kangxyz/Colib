/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Fibration.CanonicalFiberMap
public import Colib.KTheory.Waldhausen.Additivity.DiagonalNaturality
public import Colib.KTheory.Waldhausen.Functoriality
public import Colib.KTheory.Waldhausen.ZeroFunctor
public import Mathlib.Topology.Homotopy.Contractible

/-! # The unchanged cofibration category with every morphism weak

All Waldhausen axioms are derived from the original structure. The actual
zero-to-identity transformation gives a contraction of the original
S-realization, fixed at its chosen zero throughout.


Implementation provenance:
`Quillen/Waldhausen/Fibration/AllWeak/Basic.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology
open CategoryTheory CategoryTheory.Limits
open scoped Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.AllWeak
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- Keep the original category, cofibrations, and zero, and declare every map weak. -/
def waldhausenStructure : Structure C where
  zero := W.zero
  isZero := W.isZero
  cof := W.cof
  weq := ⊤
  cof_multiplicative := W.cof_multiplicative
  weq_multiplicative := inferInstance
  cof_iso := W.cof_iso
  weq_iso := by intro X Y f hf; trivial
  cof_zero := W.cof_zero
  pushout_exists := W.pushout_exists
  cof_pushout := W.cof_pushout
  gluing := by intros; trivial

/-- The inclusion of the original weak class changes no other data. -/
def nested : NestedWeakEquivalences W where
  coarse := waldhausenStructure W
  cof_eq := rfl
  zero_eq := rfl
  le_weq := by intro X Y f hf; trivial

@[simp] theorem cof_eq : (waldhausenStructure W).cof = W.cof := rfl
@[simp] theorem zero_eq : (waldhausenStructure W).zero = W.zero := rfl
@[simp] theorem weak {X Y : C} (f : X ⟶ Y) : (waldhausenStructure W).weq f := trivial
@[simp] theorem acyclic (X : C) : Acyclic (waldhausenStructure W) X := trivial

/-- Saturation here is proved by the literal top morphism property. -/
instance saturated : (waldhausenStructure W).weq.HasTwoOutOfThreeProperty := by
  change (⊤ : MorphismProperty C).HasTwoOutOfThreeProperty
  infer_instance

instance nested_saturated : (nested W).coarse.weq.HasTwoOutOfThreeProperty := saturated W

/-- The extension axiom holds for every actual cofiber square. -/
theorem extensionAxiom : ExtensionAxiom (waldhausenStructure W) where
  extension := by intros; trivial

/-- The original unique zero-to-object arrows form the contraction transformation. -/
def zeroToIdentity : zeroFunctor (waldhausenStructure W) ⟶ 𝟭 C where
  app X := W.isZero.to_ X
  naturality _ _ _ := W.isZero.eq_of_src _ _

@[simp] theorem zeroToIdentity_app (X : C) :
    (zeroToIdentity W).app X = W.isZero.to_ X := rfl

/-- The actual realization homotopy runs from the chosen zero to the identity. -/
def zeroToIdentityHomotopy :
    (ContinuousMap.const (waldhausenStructure W).Delooping
      (waldhausenStructure W).kBasepoint).Homotopy
        (ContinuousMap.id (waldhausenStructure W).Delooping) := by
  let H := weakNaturalTransformationRealizationHomotopy
    (waldhausenStructure W) (waldhausenStructure W)
    (zeroFunctor_isExact _ _) (IsExact.id _ _) (zeroToIdentity W) (fun _ ↦ trivial)
  exact {
    toContinuousMap := H.toContinuousMap
    map_zero_left x := (H.map_zero_left x).trans
      (DFunLike.congr_fun (deloopingMap_zeroFunctor _ _) x)
    map_one_left x := (H.map_one_left x).trans
      (DFunLike.congr_fun (congrArg TopCat.Hom.hom (deloopingMap_id _)) x) }

/-- The original zero track is constant, not just homotopic to a constant track. -/
@[simp] theorem zeroToIdentityHomotopy_fixed_zero (t : unitInterval) :
    zeroToIdentityHomotopy W (t, (waldhausenStructure W).kBasepoint) =
      (waldhausenStructure W).kBasepoint :=
  weakNaturalTransformationRealizationHomotopy_fixed_zero
    (waldhausenStructure W) (waldhausenStructure W)
    (zeroFunctor_isExact _ _) (IsExact.id _ _) (zeroToIdentity W) (fun _ ↦ trivial)
    rfl rfl t

/-- Reverse the original zero-to-identity homotopy to obtain an actual contraction. -/
def contraction : (ContinuousMap.id (waldhausenStructure W).Delooping).Homotopy
    (ContinuousMap.const _ (waldhausenStructure W).kBasepoint) :=
  (zeroToIdentityHomotopy W).symm

@[simp] theorem contraction_fixed_zero (t : unitInterval) :
    contraction W (t, (waldhausenStructure W).kBasepoint) =
      (waldhausenStructure W).kBasepoint :=
  zeroToIdentityHomotopy_fixed_zero W (unitInterval.symm t)

/-- The actual all-weak S-realization is contractible. -/
instance delooping_contractible : ContractibleSpace (waldhausenStructure W).Delooping :=
  (contractible_iff_id_nullhomotopic _).mpr
    ⟨(waldhausenStructure W).kBasepoint, ⟨contraction W⟩⟩

end CategoryTheory.Waldhausen.Fibration.AllWeak
