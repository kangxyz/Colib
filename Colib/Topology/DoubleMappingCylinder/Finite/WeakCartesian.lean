/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.DoubleMappingCylinder.Finite.Cartesian
public import Colib.Topology.HomotopyPullback.WeakPasting
public import Colib.Topology.OpenGluing.GlobalWeakComparison
public import Colib.Topology.HomotopyPullback.WeakCartesianSource

/-!
# Weak-fiber finite normalization and original endpoint comparisons

The original finite normalization retains its actual overlap product charts.
Fixing a base point and its band parameter identifies each overlap strict
fiber map with the original edge strict-fiber map. The genuine normalized
weak comparison then pastes with the original endpoint pullback comparison.
No homotopy inverse for a weak edge is chosen or assumed.


Implementation provenance:
`Quillen/Topology/DoubleMappingCylinder/Finite/WeakCartesian.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
open unitInterval
universe u v
namespace TopCat.DoubleCylinder.FiniteNormalization

/-- A product chart over a product base identifies the actual strict fiber
with the original strict fiber at the fixed base and parameter. -/
def productChartFiberHomeomorph
    {X Y Z W : Type u} {P : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace P] [TopologicalSpace Z] [TopologicalSpace W]
    (p : C(X, Y)) (q : C(Z, W)) (h : X × P ≃ₜ Z) (e : Y × P ≃ₜ W)
    (hq : ∀ x t, q (h (x, t)) = e (p x, t)) (y : Y) (t : P) :
    {z : Z // q z = e (y,t)} ≃ₜ {x : X // p x = y} := by
  have coord (z : {z : Z // q z = e (y,t)}) :
      (p (h.symm z.val).1,(h.symm z.val).2) = (y,t) :=
    e.injective ((hq (h.symm z.val).1 (h.symm z.val).2).symm.trans
      ((congrArg q (h.apply_symm_apply z.val)).trans z.property))
  exact {
    toFun z := ⟨(h.symm z.val).1,congrArg Prod.fst (coord z)⟩
    invFun x := ⟨h (x.val,t),(hq x.val t).trans
      (congrArg e (Prod.ext x.property rfl))⟩
    left_inv z := by
      apply Subtype.ext
      change h ((h.symm z.val).1,t) = z.val
      have ht : (h.symm z.val).2 = t := congrArg Prod.snd (coord z)
      have hz : ((h.symm z.val).1,t) = h.symm z.val := Prod.ext rfl ht.symm
      exact (congrArg h hz).trans (h.apply_symm_apply z.val)
    right_inv x := by
      apply Subtype.ext
      exact congrArg Prod.fst (h.symm_apply_apply (x.val,t))
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }

variable {A B C D A' B' C' D' : TopCat.{u}}
  {f : A ⟶ B} {g : A ⟶ C} {f' : A' ⟶ B'} {g' : A' ⟶ C'}
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  {l' : A' ⊗ TopCat.I ⟶ D'} {e' : TopCat.of (B' ⊕ C') ⟶ D'}
  (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
  (sq' : IsPushout (TopCat.intervalEndpoints A') (endMap f' g') l' e')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g')

/-- The original overlap source fiber, with its band parameter fixed, is
the original attaching-space strict fiber. -/
def overlapSourceFiberHomeomorph (x : A') (t : Parameter) :
    {z : (data sq' a b c wf wg).R //
      ((data sq' a b c wf wg).k0 ≫ (data sq' a b c wf wg).q0) z =
        overlapHomeomorph sq' (x,t)} ≃ₜ {z : A // a z = x} :=
  productChartFiberHomeomorph (P := Parameter) a.hom
    ((data sq' a b c wf wg).k0 ≫ (data sq' a b c wf wg).q0).hom
    (Homeomorph.refl _) (overlapHomeomorph sq')
    (fun _ _ ↦ rfl) x t

/-- The original overlap source fiber, with its band parameter fixed, is
the original attaching-space strict fiber. -/
def overlapSourceFiberHomeomorph1 (x : A') (t : Parameter) :
    {z : (data sq' a b c wf wg).R //
      ((data sq' a b c wf wg).k1 ≫ (data sq' a b c wf wg).q1) z =
        overlapHomeomorph sq' (x,t)} ≃ₜ {z : A // a z = x} :=
  productChartFiberHomeomorph (P := Parameter) a.hom
    ((data sq' a b c wf wg).k1 ≫ (data sq' a b c wf wg).q1).hom
    (Homeomorph.refl _) (overlapHomeomorph sq')
    (fun _ _ ↦ rfl) x t

/-- The original left overlap target fiber is the actual strict fiber of
the original left edge pullback, through the unchanged band chart. -/
def overlapTargetFiberHomeomorph0 (x : A') (t : Parameter) :
    {z : (data sq' a b c wf wg).Q0 //
      (data sq' a b c wf wg).q0 z = overlapHomeomorph sq' (x,t)} ≃ₜ
      {z : {z : A' × B // b z.2 = f' z.1} //
        HomotopyPullback.strictBaseProjection b.hom f'.hom z = x} :=
  productChartFiberHomeomorph (P := Parameter) (HomotopyPullback.strictBaseProjection b.hom f'.hom)
    (data sq' a b c wf wg).q0.hom
    (leftPullbackBandHomeomorph f' g' sq' lower upper zero_lt_upper b)
    (overlapHomeomorph sq') (fun _ _ ↦ rfl) x t

/-- The original right overlap target has the matching actual fiber chart. -/
def overlapTargetFiberHomeomorph1 (x : A') (t : Parameter) :
    {z : (data sq' a b c wf wg).Q1 //
      (data sq' a b c wf wg).q1 z = overlapHomeomorph sq' (x,t)} ≃ₜ
      {z : {z : A' × C // c z.2 = g' z.1} //
        HomotopyPullback.strictBaseProjection c.hom g'.hom z = x} :=
  productChartFiberHomeomorph (P := Parameter) (HomotopyPullback.strictBaseProjection c.hom g'.hom)
    (data sq' a b c wf wg).q1.hom
    (rightPullbackBandHomeomorph f' g' sq' lower upper lower_lt_one c)
    (overlapHomeomorph sq') (fun _ _ ↦ rfl) x t

/-- The original left edge's weak strict fibers remain weak in the actual
normalized overlap; this is an exact fiber chart change, not a product
weakness inference. -/
theorem overlapMap0_strictFibers_isWeak
    (hf : ∀ x : A', IsWeakHomotopyEquivalence
      (HomotopyFiber.strictMapOver a.hom
        (HomotopyPullback.strictBaseProjection b.hom f'.hom) (leftEdge a b wf) rfl x))
    (z : Overlap sq') :
    IsWeakHomotopyEquivalence (HomotopyFiber.strictMapOver
      ((data sq' a b c wf wg).k0 ≫ (data sq' a b c wf wg).q0).hom
      (data sq' a b c wf wg).q0.hom (data sq' a b c wf wg).k0.hom rfl z) := by
  obtain ⟨⟨x,t⟩,rfl⟩ := (overlapHomeomorph sq').surjective z
  let es := overlapSourceFiberHomeomorph sq' a b c wf wg x t
  let et := overlapTargetFiberHomeomorph0 sq' a b c wf wg x t
  have he : et.toHomotopyEquiv.toFun.comp
      (HomotopyFiber.strictMapOver
        ((data sq' a b c wf wg).k0 ≫ (data sq' a b c wf wg).q0).hom
        (data sq' a b c wf wg).q0.hom (data sq' a b c wf wg).k0.hom rfl
        (overlapHomeomorph sq' (x,t))) =
      (HomotopyFiber.strictMapOver a.hom
        (HomotopyPullback.strictBaseProjection b.hom f'.hom) (leftEdge a b wf) rfl x).comp
          es.toHomotopyEquiv.toFun := by
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    exact congrArg Prod.fst
      ((leftPullbackBandHomeomorph f' g' sq' lower upper zero_lt_upper b).symm_apply_apply
        (leftEdge a b wf z.val.1,z.val.2))
  exact (he ▸ (hf x).comp
    (isWeakHomotopyEquivalence_of_homotopyEquiv es.toHomotopyEquiv)).of_comp_right
      (isWeakHomotopyEquivalence_of_homotopyEquiv et.toHomotopyEquiv)

/-- The original right edge's weak strict fibers remain weak in the actual
normalized overlap; this is an exact fiber chart change, not a product
weakness inference. -/
theorem overlapMap1_strictFibers_isWeak
    (hf : ∀ x : A', IsWeakHomotopyEquivalence
      (HomotopyFiber.strictMapOver a.hom
        (HomotopyPullback.strictBaseProjection c.hom g'.hom) (rightEdge a c wg) rfl x))
    (z : Overlap sq') :
    IsWeakHomotopyEquivalence (HomotopyFiber.strictMapOver
      ((data sq' a b c wf wg).k1 ≫ (data sq' a b c wf wg).q1).hom
      (data sq' a b c wf wg).q1.hom (data sq' a b c wf wg).k1.hom rfl z) := by
  obtain ⟨⟨x,t⟩,rfl⟩ := (overlapHomeomorph sq').surjective z
  let es := overlapSourceFiberHomeomorph1 sq' a b c wf wg x t
  let et := overlapTargetFiberHomeomorph1 sq' a b c wf wg x t
  have he : et.toHomotopyEquiv.toFun.comp
      (HomotopyFiber.strictMapOver
        ((data sq' a b c wf wg).k1 ≫ (data sq' a b c wf wg).q1).hom
        (data sq' a b c wf wg).q1.hom (data sq' a b c wf wg).k1.hom rfl
        (overlapHomeomorph sq' (x,t))) =
      (HomotopyFiber.strictMapOver a.hom
        (HomotopyPullback.strictBaseProjection c.hom g'.hom) (rightEdge a c wg) rfl x).comp
          es.toHomotopyEquiv.toFun := by
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    exact congrArg Prod.fst
      ((rightPullbackBandHomeomorph f' g' sq' lower upper lower_lt_one c).symm_apply_apply
        (rightEdge a c wg z.val.1,z.val.2))
  exact (he ▸ (hf x).comp
    (isWeakHomotopyEquivalence_of_homotopyEquiv es.toHomotopyEquiv)).of_comp_right
      (isWeakHomotopyEquivalence_of_homotopyEquiv et.toHomotopyEquiv)

section WeakFibers
variable
  (ha : HomotopyLiftingProperty a.hom) (hb : HomotopyLiftingProperty b.hom)
  (hc : HomotopyLiftingProperty c.hom)
  (hgraph : ∀ (S : Type u) [TopologicalSpace S] [CompactSpace S] [LocallyCompactSpace S]
    (v : C(S, Overlap sq')), IsClosed (Set.ofPred (fun z : S × Overlap sq' ↦ v z.1 = z.2)))
  (hf0 : ∀ x : A', IsWeakHomotopyEquivalence
    (HomotopyFiber.strictMapOver a.hom
      (HomotopyPullback.strictBaseProjection b.hom f'.hom) (leftEdge a b wf) rfl x))
  (hf1 : ∀ x : A', IsWeakHomotopyEquivalence
    (HomotopyFiber.strictMapOver a.hom
      (HomotopyPullback.strictBaseProjection c.hom g'.hom) (rightEdge a c wg) rfl x))
include ha hb hc hgraph hf0 hf1

/-- The original finite normalized left chart comparison is weak from
weak original strict edge fibers and genuine vertical fibrations. -/
theorem normalizedLeftChart_isWeak_of_weak_fibers :
    IsWeakHomotopyEquivalence (NData sq' a b c wf wg).normalized.leftComparison :=
  (NData sq' a b c wf wg).leftComparison_isWeakHomotopyEquivalence_of_weak_fibers
    (leftCollar_isOpen f' g' sq' upper) (rightCollar_isOpen f' g' sq' lower)
    (collar_cover f' g' sq' upper lower (by change (1 / 4 : ℝ) < 3 / 4; norm_num))
    (endProjection0_lifting sq' b hb) (endProjection1_lifting sq' c hc)
    (overlap_lifting sq' a b c wf wg ha) hgraph
    (overlapMap0_strictFibers_isWeak sq' a b c wf wg hf0)
    (overlapMap1_strictFibers_isWeak sq' a b c wf wg hf1)

/-- The unchanged normalized right chart comparison has the same weak-input
conclusion. -/
theorem normalizedRightChart_isWeak_of_weak_fibers :
    IsWeakHomotopyEquivalence (NData sq' a b c wf wg).normalized.rightComparison :=
  (NData sq' a b c wf wg).rightComparison_isWeakHomotopyEquivalence_of_weak_fibers
    (leftCollar_isOpen f' g' sq' upper) (rightCollar_isOpen f' g' sq' lower)
    (collar_cover f' g' sq' upper lower (by change (1 / 4 : ℝ) < 3 / 4; norm_num))
    (endProjection0_lifting sq' b hb) (endProjection1_lifting sq' c hc)
    (overlap_lifting sq' a b c wf wg ha) hgraph
    (overlapMap0_strictFibers_isWeak sq' a b c wf wg hf0)
    (overlapMap1_strictFibers_isWeak sq' a b c wf wg hf1)

/-- Pasting the actual left collar endpoint pullback with its weak normalized
chart retains the prescribed original constant-path comparison. -/
theorem normalizedLeftEndComparison_isWeak_of_weak_fibers :
    IsWeakHomotopyEquivalence
      (HomotopyPullback.comparison (NData sq' a b c wf wg).normalized.projection.hom
        (Subdivision.leftEnd (e := e')).hom b.hom (normalizedLeft sq' a b c wf wg)
        (normalizedLeft_square sq' a b c wf wg)) :=
  HomotopyPullback.comparison_paste_isWeakHomotopyEquivalence b.hom (endProjection0 sq' b).hom
    (NData sq' a b c wf wg).normalized.projection.hom
    (RetractionPullback.inclusion
      (leftCollarStrongDeformationRetract f' g' sq' upper zero_lt_upper) b)
    (NData sq' a b c wf wg).normalized.totalLeft.hom
    (leftCollarInclusion f' g' sq' upper zero_lt_upper).hom
    (NData sq' a b c wf wg).normalized.leftBaseInclusion rfl
    (NData sq' a b c wf wg).normalized.left_square
    (isWeakHomotopyEquivalence_of_homotopyEquiv
      (RetractionPullback.endpointHomotopyEquiv
        (leftCollarStrongDeformationRetract f' g' sq' upper zero_lt_upper) b hb))
    (normalizedLeftChart_isWeak_of_weak_fibers sq' a b c wf wg ha hb hc hgraph hf0 hf1)

/-- The corresponding original normalized right endpoint comparison is weak. -/
theorem normalizedRightEndComparison_isWeak_of_weak_fibers :
    IsWeakHomotopyEquivalence
      (HomotopyPullback.comparison (NData sq' a b c wf wg).normalized.projection.hom
        (Subdivision.rightEnd (e := e')).hom c.hom (normalizedRight sq' a b c wf wg)
        (normalizedRight_square sq' a b c wf wg)) :=
  HomotopyPullback.comparison_paste_isWeakHomotopyEquivalence c.hom (endProjection1 sq' c).hom
    (NData sq' a b c wf wg).normalized.projection.hom
    (RetractionPullback.inclusion
      (rightCollarStrongDeformationRetract f' g' sq' lower lower_lt_one) c)
    (NData sq' a b c wf wg).normalized.totalEnd.hom
    (rightCollarInclusion f' g' sq' lower lower_lt_one).hom
    (NData sq' a b c wf wg).normalized.rightBaseInclusion rfl
    (NData sq' a b c wf wg).normalized.right_square
    (isWeakHomotopyEquivalence_of_homotopyEquiv
      (RetractionPullback.endpointHomotopyEquiv
        (rightCollarStrongDeformationRetract f' g' sq' lower lower_lt_one) c hc))
    (normalizedRightChart_isWeak_of_weak_fibers sq' a b c wf wg ha hb hc hgraph hf0 hf1)

/-- The actual left endpoint square of the original double-cylinder map is
weak-cartesian from original weak strict fibers, with its canonical map intact. -/
theorem leftEndComparison_isWeak_of_weak_fibers :
    IsWeakHomotopyEquivalence
      (HomotopyPullback.comparison (DoubleCylinder.map sq sq' a b c wf wg).hom
        (Subdivision.leftEnd (e := e')).hom b.hom (Subdivision.leftEnd (e := e)).hom
        (left_square sq sq' a b c wf wg)) :=
  HomotopyPullback.comparison_isWeakHomotopyEquivalence_of_sourceMap
    (DoubleCylinder.map sq sq' a b c wf wg).hom
    (NData sq' a b c wf wg).normalized.projection.hom (Subdivision.leftEnd (e := e')).hom
    b.hom (Subdivision.leftEnd (e := e)).hom (normalizedLeft sq' a b c wf wg)
    (left_square sq sq' a b c wf wg) (normalizedLeft_square sq' a b c wf wg)
    (normalizationEquiv sq sq' a b c wf wg).toFun
    (isWeakHomotopyEquivalence_of_homotopyEquiv (normalizationEquiv sq sq' a b c wf wg))
    (normalizationEquiv_over sq sq' a b c wf wg)
    (by ext x; exact normalizationEquiv_left sq sq' a b c wf wg x)
    (normalizedLeftEndComparison_isWeak_of_weak_fibers sq' a b c wf wg ha hb hc hgraph hf0 hf1)

/-- The symmetric original right endpoint comparison is weak, with the full
constant path and source endpoint unchanged. -/
theorem rightEndComparison_isWeak_of_weak_fibers :
    IsWeakHomotopyEquivalence
      (HomotopyPullback.comparison (DoubleCylinder.map sq sq' a b c wf wg).hom
        (Subdivision.rightEnd (e := e')).hom c.hom (Subdivision.rightEnd (e := e)).hom
        (right_square sq sq' a b c wf wg)) :=
  HomotopyPullback.comparison_isWeakHomotopyEquivalence_of_sourceMap
    (DoubleCylinder.map sq sq' a b c wf wg).hom
    (NData sq' a b c wf wg).normalized.projection.hom (Subdivision.rightEnd (e := e')).hom
    c.hom (Subdivision.rightEnd (e := e)).hom (normalizedRight sq' a b c wf wg)
    (right_square sq sq' a b c wf wg) (normalizedRight_square sq' a b c wf wg)
    (normalizationEquiv sq sq' a b c wf wg).toFun
    (isWeakHomotopyEquivalence_of_homotopyEquiv (normalizationEquiv sq sq' a b c wf wg))
    (normalizationEquiv_over sq sq' a b c wf wg)
    (by ext x; exact normalizationEquiv_right sq sq' a b c wf wg x)
    (normalizedRightEndComparison_isWeak_of_weak_fibers sq' a b c wf wg ha hb hc hgraph hf0 hf1)

end WeakFibers

/-- Whole weak edge comparisons suffice: their actual projections are
fibrations, so the original strict-fiber weakness is a theorem. -/
theorem leftEndComparison_isWeak_of_weak_edges
    (ha : HomotopyLiftingProperty a.hom) (hb : HomotopyLiftingProperty b.hom)
    (hc : HomotopyLiftingProperty c.hom)
    (hgraph : ∀ (S : Type u) [TopologicalSpace S] [CompactSpace S] [LocallyCompactSpace S]
      (v : C(S, Overlap sq')), IsClosed (Set.ofPred (fun z : S × Overlap sq' ↦ v z.1 = z.2)))
    (hf0 : IsWeakHomotopyEquivalence (leftEdge a b wf))
    (hf1 : IsWeakHomotopyEquivalence (rightEdge a c wg)) :
    IsWeakHomotopyEquivalence
      (HomotopyPullback.comparison (DoubleCylinder.map sq sq' a b c wf wg).hom
        (Subdivision.leftEnd (e := e')).hom b.hom (Subdivision.leftEnd (e := e)).hom
        (left_square sq sq' a b c wf wg)) :=
  leftEndComparison_isWeak_of_weak_fibers sq sq' a b c wf wg ha hb hc hgraph
    (fun x ↦ HomotopyFiber.strictMapOver_isWeakHomotopyEquivalence a.hom
      (HomotopyPullback.strictBaseProjection b.hom f'.hom) (leftEdge a b wf) rfl x ha
      (HomotopyLiftingProperty.baseChange _ _ hb) hf0)
    (fun x ↦ HomotopyFiber.strictMapOver_isWeakHomotopyEquivalence a.hom
      (HomotopyPullback.strictBaseProjection c.hom g'.hom) (rightEdge a c wg) rfl x ha
      (HomotopyLiftingProperty.baseChange _ _ hc) hf1)

/-- Matching weak whole-edge sufficient form for the original right endpoint. -/
theorem rightEndComparison_isWeak_of_weak_edges
    (ha : HomotopyLiftingProperty a.hom) (hb : HomotopyLiftingProperty b.hom)
    (hc : HomotopyLiftingProperty c.hom)
    (hgraph : ∀ (S : Type u) [TopologicalSpace S] [CompactSpace S] [LocallyCompactSpace S]
      (v : C(S, Overlap sq')), IsClosed (Set.ofPred (fun z : S × Overlap sq' ↦ v z.1 = z.2)))
    (hf0 : IsWeakHomotopyEquivalence (leftEdge a b wf))
    (hf1 : IsWeakHomotopyEquivalence (rightEdge a c wg)) :
    IsWeakHomotopyEquivalence
      (HomotopyPullback.comparison (DoubleCylinder.map sq sq' a b c wf wg).hom
        (Subdivision.rightEnd (e := e')).hom c.hom (Subdivision.rightEnd (e := e)).hom
        (right_square sq sq' a b c wf wg)) :=
  rightEndComparison_isWeak_of_weak_fibers sq sq' a b c wf wg ha hb hc hgraph
    (fun x ↦ HomotopyFiber.strictMapOver_isWeakHomotopyEquivalence a.hom
      (HomotopyPullback.strictBaseProjection b.hom f'.hom) (leftEdge a b wf) rfl x ha
      (HomotopyLiftingProperty.baseChange _ _ hb) hf0)
    (fun x ↦ HomotopyFiber.strictMapOver_isWeakHomotopyEquivalence a.hom
      (HomotopyPullback.strictBaseProjection c.hom g'.hom) (rightEdge a c wg) rfl x ha
      (HomotopyLiftingProperty.baseChange _ _ hc) hf1)

end TopCat.DoubleCylinder.FiniteNormalization
