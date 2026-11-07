/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.Regular.CoherentResolution
public import Colib.CategoryTheory.SmallModel.Exact
public import Colib.KTheory.Quillen.Resolution.Theorem
public import Colib.KTheory.Quillen.Equivalence

/-!
# Actual vector-bundle resolutions in the native coherent small model

The original small-model comparison factors through the genuine full subcategory
of represented vector bundles. Its lifted functor is an exact equivalence, and
actual finite resolutions descend through Mathlib's chosen equivalence.

Implementation provenance: `Quillen/Aglib/AlgebraicGeometry/Modules/LocallyFree/
Resolution/SmallModel.lean` and `Quillen/AlgebraicGeometry/Scheme/Regular/
SmallComparison.lean` at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The native vector-bundle and coherent categories replace the earlier Aglib models.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped ZeroObject

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- The actual vector-bundle property of the represented coherent object. -/
def coherentSmallVectorBundle :
    ObjectProperty (SmallModel.{u + 1} (SheafOfModules.CoherentModules X.ringCatSheaf)) :=
  fun M => coherentVectorBundle X
    ((equivSmallModel (SheafOfModules.CoherentModules X.ringCatSheaf)).inverse.obj M)

instance coherentSmallVectorBundle_isClosedUnderIsomorphisms :
    (coherentSmallVectorBundle X).IsClosedUnderIsomorphisms where
  of_iso e h := (coherentVectorBundle X).prop_of_iso
    ((equivSmallModel (SheafOfModules.CoherentModules X.ringCatSheaf)).inverse.mapIso e) h

instance coherentSmallVectorBundle_containsZero :
    (coherentSmallVectorBundle X).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, (coherentVectorBundle X).prop_of_isZero
    ((equivSmallModel (SheafOfModules.CoherentModules X.ringCatSheaf)).inverse.map_isZero
      (isZero_zero _))⟩

instance coherentSmallVectorBundle_isExtensionClosed :
    (coherentExactStructure X).smallModel.{u + 1}.IsExtensionClosed
      (coherentSmallVectorBundle X) where
  prop_middle hS h₁ h₃ := ExactStructure.IsExtensionClosed.prop_middle
    (E := coherentExactStructure X) hS h₁ h₃

instance coherentSmallVectorBundle_isKernelClosed :
    (coherentExactStructure X).smallModel.{u + 1}.IsKernelClosed
      (coherentSmallVectorBundle X) where
  prop_kernel hS h₂ h₃ := ExactStructure.IsKernelClosed.prop_kernel
    (E := coherentExactStructure X) hS h₂ h₃

instance coherentSmallVectorBundle_isClosedUnderFiniteProducts :
    (coherentSmallVectorBundle X).IsClosedUnderFiniteProducts :=
  (coherentExactStructure X).smallModel.{u + 1}.extensionClosed_finiteProducts _

/-- The original comparison with its actual codomain restricted to vector bundles. -/
def vectorBundleSmallLift : SmallModel.{u + 1} X.Vect ⥤
    (coherentSmallVectorBundle X).FullSubcategory :=
  (coherentSmallVectorBundle X).lift
    (vectorBundleToCoherentExact X).smallModel.{u + 1}.toFunctor
    (fun M => (coherentVectorBundle X).prop_of_iso
      ((equivSmallModel (SheafOfModules.CoherentModules X.ringCatSheaf)).unitIso.app
        ((vectorBundleToCoherent X).obj ((equivSmallModel X.Vect).inverse.obj M)))
      (((equivSmallModel X.Vect).inverse.obj M).property))

instance vectorBundleSmallLift_full : (vectorBundleSmallLift X).Full := by
  dsimp [vectorBundleSmallLift, ExactFunctor.smallModel, ExactFunctor.comp,
    ExactStructure.smallModelToOriginal, ExactStructure.originalToSmallModel,
    ExactStructure.equivalenceExactFunctor, ExactStructure.equivalenceInverseExactFunctor,
    vectorBundleToCoherentExact, vectorBundleToCoherent]
  infer_instance

instance vectorBundleSmallLift_faithful : (vectorBundleSmallLift X).Faithful := by
  dsimp [vectorBundleSmallLift, ExactFunctor.smallModel, ExactFunctor.comp,
    ExactStructure.smallModelToOriginal, ExactStructure.originalToSmallModel,
    ExactStructure.equivalenceExactFunctor, ExactStructure.equivalenceInverseExactFunctor,
    vectorBundleToCoherentExact, vectorBundleToCoherent]
  infer_instance

instance vectorBundleSmallLift_additive : (vectorBundleSmallLift X).Additive := by
  dsimp [vectorBundleSmallLift]
  infer_instance

instance vectorBundleSmallLift_essSurj : (vectorBundleSmallLift X).EssSurj where
  mem_essImage Z := by
    let EV := equivSmallModel.{u + 1} X.Vect
    let EC := equivSmallModel.{u + 1} (SheafOfModules.CoherentModules X.ringCatSheaf)
    let V : X.Vect := ⟨(EC.inverse.obj Z.obj).obj, Z.property⟩
    let e : ((vectorBundleToCoherentExact X).smallModel.toFunctor).obj (EV.functor.obj V) ≅
        Z.obj :=
      EC.functor.mapIso ((vectorBundleToCoherent X).mapIso (EV.unitIso.app V).symm) ≪≫
        EC.counitIso.app Z.obj
    exact ⟨EV.functor.obj V, ⟨ObjectProperty.isoMk _ e⟩⟩

instance vectorBundleSmallLift_isEquivalence : (vectorBundleSmallLift X).IsEquivalence := {}

/-- Restricting the codomain leaves the original exact comparison unchanged. -/
def vectorBundleSmallLiftExact :
    ExactFunctor (vectorBundleExactStructure X).smallModel.{u + 1}
      (ExactSubcategory.exactStructure (coherentExactStructure X).smallModel.{u + 1}
        (coherentSmallVectorBundle X)) where
  toFunctor := vectorBundleSmallLift X
  map_conflation S hS := (vectorBundleToCoherentExact X).smallModel.map_conflation S hS

/-- The lifted equivalence reflects the actual inherited exact structure. -/
theorem vectorBundleSmallLift_conflation_iff
    (S : ShortComplex (SmallModel.{u + 1} X.Vect)) :
    (ExactSubcategory.exactStructure (coherentExactStructure X).smallModel.{u + 1}
      (coherentSmallVectorBundle X)).conflation (S.map (vectorBundleSmallLift X)) ↔
      (vectorBundleExactStructure X).smallModel.{u + 1}.conflation S := by
  let EV := equivSmallModel.{u + 1} X.Vect
  let EC := equivSmallModel.{u + 1} (SheafOfModules.CoherentModules X.ringCatSheaf)
  let T := (S.map EV.inverse).map (vectorBundleToCoherent X)
  change (T.map (EC.functor ⋙ EC.inverse)).ShortExact ↔
    (vectorBundleExactStructure X).conflation (S.map EV.inverse)
  rw [← vectorBundleToCoherent_conflation_iff]
  exact (ShortComplex.shortExact_iff_of_iso (T.mapNatIso EC.unitIso)).symm

instance vectorBundleSmallLift_asEquivalence_additive :
    (vectorBundleSmallLift X).asEquivalence.functor.Additive :=
  inferInstanceAs (vectorBundleSmallLift X).Additive

instance vectorBundleSmallLiftExact_isEquivalence :
    (vectorBundleSmallLiftExact X).toFunctor.IsEquivalence :=
  inferInstanceAs (vectorBundleSmallLift X).IsEquivalence

/-- Pullback along the lifted equivalence is precisely the existing exact structure. -/
theorem vectorBundleSmallLift_ofEquivalence :
    (ExactSubcategory.exactStructure (coherentExactStructure X).smallModel.{u + 1}
      (coherentSmallVectorBundle X)).ofEquivalence (vectorBundleSmallLift X).asEquivalence =
      (vectorBundleExactStructure X).smallModel.{u + 1} := by
  apply ExactStructure.ext_conflation
  funext S
  exact propext (vectorBundleSmallLift_conflation_iff X S)

instance vectorBundleSmallLiftExact_mapQ_isEquivalence :
    (vectorBundleSmallLiftExact X).mapQ.IsEquivalence := by
  apply ExactFunctor.mapQ_isEquivalence_of_equivalence
  · intro A B i hi
    rw [← vectorBundleSmallLift_ofEquivalence X]
    exact (ExactStructure.ofEquivalence_inflation_iff _ _ i).mpr hi
  · intro A B p hp
    rw [← vectorBundleSmallLift_ofEquivalence X]
    exact (ExactStructure.ofEquivalence_deflation_iff _ _ p).mpr hp

/-- The factorization is literally the canonical small exact functor. -/
theorem vectorBundleSmall_factor :
    (vectorBundleSmallLiftExact X).comp
      (Resolution.exactInclusion (coherentExactStructure X).smallModel.{u + 1}
        (coherentSmallVectorBundle X)) = (vectorBundleToCoherentExact X).smallModel.{u + 1} := rfl

/-- Actual finite resolutions descend with no uniform bound on their lengths. -/
theorem coherentSmallResolutionHypothesis
    (h : (coherentExactStructure X).ResolutionHypothesis (coherentVectorBundle X)) :
    (coherentExactStructure X).smallModel.{u + 1}.ResolutionHypothesis
      (coherentSmallVectorBundle X) := by
  intro M
  let E := equivSmallModel.{u + 1} (SheafOfModules.CoherentModules X.ringCatSheaf)
  obtain ⟨T⟩ := h (E.inverse.obj M)
  let T' := (coherentExactStructure X).originalToSmallModel.mapFiniteResolution
    (P' := coherentSmallVectorBundle X)
    (fun N hN => (coherentVectorBundle X).prop_of_iso (E.unitIso.app N) hN) T
  exact ⟨T'.ofIso (E.counitIso.app M)⟩

end AlgebraicGeometry.Scheme.Modules
