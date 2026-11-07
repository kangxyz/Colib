/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremB.StructuredOpposite
public import Colib.CategoryTheory.TheoremB.StructuredReversal

/-! Compatibility of the two canonical structured-comma comparisons. -/
/-! Implementation source: `Quillen/CategoryTheory/TheoremB/StructuredTransport.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual maps, paths and identity
basepoints are retained under native namespace and dependency ownership. -/
@[expose] public section

noncomputable section
open SSet TopCat Topology CategoryTheory Opposite
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.TheoremB
/-- Reparameterize a homotopy from a constant map by a path from one to zero. -/
def reversedNullhomotopy {A X Y : Type*}
    [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (g : C(A, X)) (y : Y)
    (H : (ContinuousMap.const A y).Homotopy (f.comp g)) (p : Path (1 : unitInterval) 0) :
    (f.comp g).Homotopy (ContinuousMap.const A y) where
  toFun z := H (p z.1, z.2)
  continuous_toFun := by fun_prop
  map_zero_left x := by change H (p 0, x) = _; rw [p.source]; exact H.map_one_left x
  map_one_left x := by change H (p 1, x) = _; rw [p.target]; exact H.map_zero_left x

/-- An endpoint-relative parameter homotopy gives a genuine homotopy of the
nullhomotopy lifts, with fixed source coordinate throughout. -/
def fiberLiftParameterHomotopy {A X Y : Type*}
    [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (g : C(A, X)) (y : Y)
    (H : (ContinuousMap.const A y).Homotopy (f.comp g))
    (p q : Path (1 : unitInterval) 0) (K : p.Homotopy q) :
    (HomotopyFiber.lift f y g (reversedNullhomotopy f g y H p)).Homotopy
      (HomotopyFiber.lift f y g (reversedNullhomotopy f g y H q)) where
  toFun z := ⟨(g z.2, ⟨fun t ↦ H (K (z.1, t), z.2), by fun_prop⟩), by
    change H (K (z.1, 0), z.2) = f (g z.2)
    rw [K.source]
    exact H.map_one_left z.2,
    by
      change H (K (z.1, 1), z.2) = y
      rw [K.target]
      exact H.map_zero_left z.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun z : (unitInterval × A) × unitInterval ↦ H (K (z.1.1, z.2), z.1.2))
      fun_prop
  map_zero_left x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply ContinuousMap.ext
      intro t
      exact congrArg (fun r ↦ H (r, x)) (K.map_zero_left t)
  map_one_left x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply ContinuousMap.ext
      intro t
      exact congrArg (fun r ↦ H (r, x)) (K.map_one_left t)

private theorem fiberMaps_ext {A X Y : Type*}
    [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (y : Y) (a b : C(A, HomotopyFiber f y))
    (h₁ : (HomotopyFiber.projection f y).comp a = (HomotopyFiber.projection f y).comp b)
    (h₂ : ∀ x t, (a x).1.2 t = (b x).1.2 t) : a = b := by
  ext x
  apply Subtype.ext
  apply Prod.ext
  · exact ContinuousMap.congr_fun h₁ x
  · exact ContinuousMap.ext (h₂ x)

variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- The comma equivalence carries precisely the opposite structure arrows. -/
theorem structuredCommaTransformation_op (d : D) :
    CategoryTheory.Functor.whiskerLeft (structuredArrowOpEquivalence F d).functor
      (commaTransformation F.op (op d)) = NatTrans.op (structuredCommaTransformation F d) := by
  ext X
  rfl

/-- Exact compatibility of the transported path with the opposite interval
parameter; this does not identify different paths without a homotopy. -/
theorem transportedStructuredFiberComparison_path (d : D)
    (x : ClassifyingSpace (StructuredArrow d F)) (t : unitInterval) :
    (transportedStructuredFiberComparison F d x).1.2 t =
      classifyingSpaceNaturalTransformationHomotopy (structuredCommaTransformation F d)
        (oppositeIntervalPath.{u} t, x) := by
  change (oppositeFiberHomeomorph F d
    (fiberComparison F.op (op d) ((structuredCommaOppositeEquiv F d).toFun x))).1.2 t = _
  rw [oppositeFiberHomeomorph_path, fiberComparison_path]
  change (classifyingOppositeIso D).hom
    (classifyingSpaceNaturalTransformationHomotopy (commaTransformation F.op (op d))
      (t, classifyingSpaceMap (structuredArrowOpEquivalence F d).functor
        ((classifyingOppositeIso (StructuredArrow d F)).inv x))) = _
  rw [← classifyingSpaceNaturalTransformationHomotopy_whiskerLeft,
    structuredCommaTransformation_op, classifyingNaturalTransformationHomotopy_op,
    Iso.inv_hom_id_apply]
  rfl

/-- The structure-arrow homotopy with its endpoints expressed as continuous maps. -/
def structuredCommaPositiveHomotopy (d : D) :
    (ContinuousMap.const _ (classifyingSpacePoint d)).Homotopy
      ((classifyingSpaceMap F).hom.comp (classifyingSpaceMap (StructuredArrow.proj d F)).hom) :=
  (classifyingSpaceNaturalTransformationHomotopy (structuredCommaTransformation F d)).cast
    (by rw [classifyingSpaceMap_const_direct]; rfl)
    (by simp only [classifyingSpaceMap_comp, TopCat.hom_comp])

/-- The same source projection lifted using an arbitrary reversed interval path. -/
def structuredParameterizedComparison (d : D) (p : Path (1 : unitInterval) 0) :
    C(ClassifyingSpace (StructuredArrow d F),
      HomotopyFiber (classifyingSpaceMap F).hom (classifyingSpacePoint d)) :=
  HomotopyFiber.lift _ _ (classifyingSpaceMap (StructuredArrow.proj d F)).hom
    (reversedNullhomotopy _ _ _ (structuredCommaPositiveHomotopy F d) p)

@[simp] theorem structuredParameterizedComparison_projection (d : D) (p : Path (1 : unitInterval) 0)
  :
    (HomotopyFiber.projection (classifyingSpaceMap F).hom (classifyingSpacePoint d)).comp
      (structuredParameterizedComparison F d p) =
        (classifyingSpaceMap (StructuredArrow.proj d F)).hom :=
  HomotopyFiber.projection_lift _ _ _ _

@[simp] theorem structuredParameterizedComparison_path (d : D) (p : Path (1 : unitInterval) 0)
    (x : ClassifyingSpace (StructuredArrow d F)) (t : unitInterval) :
    (structuredParameterizedComparison F d p x).1.2 t =
      classifyingSpaceNaturalTransformationHomotopy (structuredCommaTransformation F d) (p t, x) :=
        rfl

theorem structuredParameterizedComparison_opposite (d : D) :
    structuredParameterizedComparison F d oppositeIntervalPath.{u} =
      transportedStructuredFiberComparison F d := by
  apply fiberMaps_ext
  · rw [structuredParameterizedComparison_projection,
    transportedStructuredFiberComparison_projection]
  · intro x t
    exact (structuredParameterizedComparison_path F d _ x t).trans
      (transportedStructuredFiberComparison_path F d x t).symm

theorem structuredParameterizedComparison_reverse (d : D) :
    structuredParameterizedComparison F d reversedIntervalPath = structuredFiberComparison F d := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply ContinuousMap.ext
    intro t
    rfl

/-- The transported costructured comparison is homotopic to the canonical
structured comparison through actual fiber maps, keeping source projection fixed. -/
def structuredFiberComparisonTransportHomotopy (d : D) :
    (transportedStructuredFiberComparison F d).Homotopy (structuredFiberComparison F d) := by
  let H : (structuredParameterizedComparison F d oppositeIntervalPath.{u}).Homotopy
      (structuredParameterizedComparison F d reversedIntervalPath) :=
    fiberLiftParameterHomotopy (classifyingSpaceMap F).hom
      (classifyingSpaceMap (StructuredArrow.proj d F)).hom (classifyingSpacePoint d)
      (structuredCommaPositiveHomotopy F d) oppositeIntervalPath.{u} reversedIntervalPath
      oppositeIntervalHomotopy.{u}
  exact H.cast (structuredParameterizedComparison_opposite F d)
    (structuredParameterizedComparison_reverse F d)
@[simp] theorem structuredFiberComparisonTransportHomotopy_projection (d : D)
    (s : unitInterval) (x : ClassifyingSpace (StructuredArrow d F)) :
    (structuredFiberComparisonTransportHomotopy F d (s, x)).1.1 =
      classifyingSpaceMap (StructuredArrow.proj d F) x := rfl

/-- The comparison transport also fixes the exact constant-path identity basepoint. -/
@[simp] theorem structuredFiberComparisonTransportHomotopy_identity (c : C) (s : unitInterval) :
    structuredFiberComparisonTransportHomotopy F (F.obj c)
      (s, classifyingSpacePoint (StructuredArrow.mk (𝟙 (F.obj c)))) =
      HomotopyFiber.basepoint (classifyingSpaceMap F).hom (classifyingSpacePoint (F.obj c))
        (classifyingSpacePoint c) (classifyingSpaceMap_point F c) := by
  apply Subtype.ext
  apply Prod.ext
  · exact classifyingSpaceMap_point (StructuredArrow.proj (F.obj c) F) _
  · apply ContinuousMap.ext
    intro t
    exact (classifyingSpaceNaturalTransformationBasedHomotopy
      (structuredCommaTransformation F (F.obj c)) (StructuredArrow.mk (𝟙 (F.obj c))) rfl rfl).eq_snd
      (oppositeIntervalHomotopy.{u} (s, t)) rfl |>.trans (classifyingSpaceMap_point _ _)

/-- Transport a proved local opposite-comma equivalence, retaining the exact
canonical structured comparison as forward map. This is only transport;
it does not supply the open global Theorem B realization theorem. -/
def transportStructuredFiberEquivalence (d : D)
    (e : ContinuousMap.HomotopyEquiv
      (ClassifyingSpace (CostructuredArrow F.op (op d)))
      (HomotopyFiber (classifyingSpaceMap F.op).hom (classifyingSpacePoint (op d))))
    (he : e.toFun = fiberComparison F.op (op d)) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (StructuredArrow d F))
      (HomotopyFiber (classifyingSpaceMap F).hom (classifyingSpacePoint d)) :=
  TheoremA.homotopyEquivWithMap
    ((structuredCommaOppositeEquiv F d).trans
      (e.trans (oppositeFiberHomeomorph F d).toHomotopyEquiv))
    (structuredFiberComparison F d) (by
      have h : (structuredFiberComparison F d).Homotopic
          (transportedStructuredFiberComparison F d) :=
        ⟨(structuredFiberComparisonTransportHomotopy F d).symm⟩
      change (structuredFiberComparison F d).Homotopic
        (((oppositeFiberHomeomorph F d : C(_, _)).comp e.toFun).comp
          (structuredCommaOppositeEquiv F d).toFun)
      rw [he]
      exact h)

@[simp] theorem transportStructuredFiberEquivalence_toFun (d : D)
    (e : ContinuousMap.HomotopyEquiv
      (ClassifyingSpace (CostructuredArrow F.op (op d)))
      (HomotopyFiber (classifyingSpaceMap F.op).hom (classifyingSpacePoint (op d))))
    (he : e.toFun = fiberComparison F.op (op d)) :
    (transportStructuredFiberEquivalence F d e he).toFun = structuredFiberComparison F d := rfl

end CategoryTheory.TheoremB
