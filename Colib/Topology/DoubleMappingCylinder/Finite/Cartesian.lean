/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.DoubleMappingCylinder.Finite.Comparison
public import Colib.Topology.OpenGluing.CartesianCharts
public import Colib.Topology.HomotopyPullback.RetractionEndpoint
public import Colib.Topology.HomotopyPullback.Pasting
public import Colib.Topology.HomotopyPullback.CartesianTransport

/-! Canonical chart comparisons for the instantiated finite-cube
normalization. -/
/-! Implementation provenance: adapted from
`Quillen/Topology/DoubleMappingCylinder/Finite/Cartesian.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual maps and hypotheses. -/
@[expose] public section

noncomputable section
open Topology
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
open unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace TopCat.DoubleCylinder.FiniteNormalization
variable {A B C D A' B' C' D' : TopCat.{u}}
  {f : A ⟶ B} {g : A ⟶ C} {f' : A' ⟶ B'} {g' : A' ⟶ C'}
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  {l' : A' ⊗ TopCat.I ⟶ D'} {e' : TopCat.of (B' ⊕ C') ⟶ D'}
  (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
  (sq' : IsPushout (TopCat.intervalEndpoints A') (endMap f' g') l' e')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g')
  (ha : HomotopyLiftingProperty a.hom) (hb : HomotopyLiftingProperty b.hom)
  (hc : HomotopyLiftingProperty c.hom)
  (E : ContinuousMap.HomotopyEquiv A {z : A' × B // b z.2 = f' z.1})
  (he : E.toFun = leftEdge a b wf)
  (F : ContinuousMap.HomotopyEquiv A {z : A' × C // c z.2 = g' z.1})
  (hf : F.toFun = rightEdge a c wg)

theorem rightSet_eq : RightSet sq' = upperBaseCollar (reflectedHeight (height f' g' sq')) := by
  ext x
  change (1 / 4 : ℝ) < (height f' g' sq' x : ℝ) ↔ 1 - (height f' g' sq' x : ℝ) < 3 / 4
  constructor <;> intro h <;> linarith

/-- The genuine left pullback chart maps homotopy-cartesianly into the
actual normalized total. -/
def leftChartEquiv : ContinuousMap.HomotopyEquiv (End0 sq' b)
    (HomotopyPullback (NData sq' a b c wf wg).normalized.projection.hom
      (NData sq' a b c wf wg).normalized.leftBaseInclusion) :=
  (NData sq' a b c wf wg).leftChartHomotopyEquiv (height f' g' sq') rfl (rightSet_eq sq')
    (endProjection0_lifting sq' b hb) (endProjection1_lifting sq' c hc)
    (overlap_lifting sq' a b c wf wg ha)
    (overlapEquiv0 sq' a b c wf wg E) (overlapEquiv0_toFun sq' a b c wf wg E he)
    (overlapEquiv1 sq' a b c wf wg F) (overlapEquiv1_toFun sq' a b c wf wg F hf)

@[simp] theorem leftChartEquiv_toFun :
    (leftChartEquiv sq' a b c wf wg ha hb hc E he F hf).toFun =
      (NData sq' a b c wf wg).normalized.leftComparison :=
  (NData sq' a b c wf wg).leftChartHomotopyEquiv_toFun _ _ _ _ _ _ _ _ _ _

/-- The genuine right pullback chart has the corresponding canonical
homotopy-cartesian comparison into the normalized total. -/
def rightChartEquiv : ContinuousMap.HomotopyEquiv (End1 sq' c)
    (HomotopyPullback (NData sq' a b c wf wg).normalized.projection.hom
      (NData sq' a b c wf wg).normalized.rightBaseInclusion) :=
  (NData sq' a b c wf wg).rightChartHomotopyEquiv (height f' g' sq') rfl (rightSet_eq sq')
    (endProjection0_lifting sq' b hb) (endProjection1_lifting sq' c hc)
    (overlap_lifting sq' a b c wf wg ha)
    (overlapEquiv0 sq' a b c wf wg E) (overlapEquiv0_toFun sq' a b c wf wg E he)
    (overlapEquiv1 sq' a b c wf wg F) (overlapEquiv1_toFun sq' a b c wf wg F hf)

@[simp] theorem rightChartEquiv_toFun :
    (rightChartEquiv sq' a b c wf wg ha hb hc E he F hf).toFun =
      (NData sq' a b c wf wg).normalized.rightComparison :=
  (NData sq' a b c wf wg).rightChartHomotopyEquiv_toFun _ _ _ _ _ _ _ _ _ _

/-- The original left endpoint space mapped into the normalized total space through its
collar-pullback inclusion and the normalized left-end inclusion. -/
abbrev normalizedLeft : C(B, (NData sq' a b c wf wg).normalized.Total) :=
  (NData sq' a b c wf wg).normalized.totalLeft.hom.comp
    (RetractionPullback.inclusion
      (leftCollarStrongDeformationRetract f' g' sq' upper zero_lt_upper) b)
/-- The original right endpoint space mapped into the normalized total space through its
collar-pullback inclusion and the normalized right-end inclusion. -/
abbrev normalizedRight : C(C, (NData sq' a b c wf wg).normalized.Total) :=
  (NData sq' a b c wf wg).normalized.totalEnd.hom.comp
    (RetractionPullback.inclusion
      (rightCollarStrongDeformationRetract f' g' sq' lower lower_lt_one) c)

theorem normalizedLeft_square :
    (NData sq' a b c wf wg).normalized.projection.hom.comp (normalizedLeft sq' a b c wf wg) =
      (Subdivision.leftEnd (e := e')).hom.comp b.hom := by
  apply ContinuousMap.ext
  intro x
  exact ConcreteCategory.congr_hom (NData sq' a b c wf wg).normalized.totalLeft_projection
    (RetractionPullback.inclusion
      (leftCollarStrongDeformationRetract f' g' sq' upper zero_lt_upper) b x)

theorem normalizedRight_square :
    (NData sq' a b c wf wg).normalized.projection.hom.comp (normalizedRight sq' a b c wf wg) =
      (Subdivision.rightEnd (e := e')).hom.comp c.hom := by
  apply ContinuousMap.ext
  intro x
  exact (NData sq' a b c wf wg).normalized.totalEnd_projection_apply
    (RetractionPullback.inclusion
      (rightCollarStrongDeformationRetract f' g' sq' lower lower_lt_one) c x)

/-- The original left endpoint is homotopy-cartesian in the normalized
total, by pasting its genuine collar pullback with the actual chart. -/
def normalizedLeftEndEquiv : ContinuousMap.HomotopyEquiv B
    (HomotopyPullback (NData sq' a b c wf wg).normalized.projection.hom
      (Subdivision.leftEnd (e := e')).hom) :=
  HomotopyPullback.pastingHomotopyEquiv b.hom (endProjection0 sq' b).hom
    (NData sq' a b c wf wg).normalized.projection.hom
    (RetractionPullback.inclusion
      (leftCollarStrongDeformationRetract f' g' sq' upper zero_lt_upper) b)
    (NData sq' a b c wf wg).normalized.totalLeft.hom
    (leftCollarInclusion f' g' sq' upper zero_lt_upper).hom
    (NData sq' a b c wf wg).normalized.leftBaseInclusion rfl
    (NData sq' a b c wf wg).normalized.left_square
    (RetractionPullback.endpointHomotopyEquiv
      (leftCollarStrongDeformationRetract f' g' sq' upper zero_lt_upper) b hb) rfl
    (leftChartEquiv sq' a b c wf wg ha hb hc E he F hf)
    (leftChartEquiv_toFun sq' a b c wf wg ha hb hc E he F hf)

@[simp] theorem normalizedLeftEndEquiv_toFun :
    (normalizedLeftEndEquiv sq' a b c wf wg ha hb hc E he F hf).toFun =
      HomotopyPullback.comparison (NData sq' a b c wf wg).normalized.projection.hom
        (Subdivision.leftEnd (e := e')).hom b.hom (normalizedLeft sq' a b c wf wg)
        (normalizedLeft_square sq' a b c wf wg) := rfl

/-- The homotopy equivalence from the original right endpoint `C` to the homotopy pullback over
the target right endpoint, obtained by pasting the endpoint retraction equivalence with the
normalized right-chart equivalence. -/
def normalizedRightEndEquiv : ContinuousMap.HomotopyEquiv C
    (HomotopyPullback (NData sq' a b c wf wg).normalized.projection.hom
      (Subdivision.rightEnd (e := e')).hom) :=
  HomotopyPullback.pastingHomotopyEquiv c.hom (endProjection1 sq' c).hom
    (NData sq' a b c wf wg).normalized.projection.hom
    (RetractionPullback.inclusion
      (rightCollarStrongDeformationRetract f' g' sq' lower lower_lt_one) c)
    (NData sq' a b c wf wg).normalized.totalEnd.hom
    (rightCollarInclusion f' g' sq' lower lower_lt_one).hom
    (NData sq' a b c wf wg).normalized.rightBaseInclusion rfl
    (NData sq' a b c wf wg).normalized.right_square
    (RetractionPullback.endpointHomotopyEquiv
      (rightCollarStrongDeformationRetract f' g' sq' lower lower_lt_one) c hc) rfl
    (rightChartEquiv sq' a b c wf wg ha hb hc E he F hf)
    (rightChartEquiv_toFun sq' a b c wf wg ha hb hc E he F hf)

@[simp] theorem normalizedRightEndEquiv_toFun :
    (normalizedRightEndEquiv sq' a b c wf wg ha hb hc E he F hf).toFun =
      HomotopyPullback.comparison (NData sq' a b c wf wg).normalized.projection.hom
        (Subdivision.rightEnd (e := e')).hom c.hom (normalizedRight sq' a b c wf wg)
        (normalizedRight_square sq' a b c wf wg) := rfl

/-- The actual left endpoint square of the original double-cylinder map. -/
theorem left_square :
    (DoubleCylinder.map sq sq' a b c wf wg).hom.comp (Subdivision.leftEnd (e := e)).hom =
      (Subdivision.leftEnd (e := e')).hom.comp b.hom := by
  ext x
  exact DoubleCylinder.map_left sq sq' a b c wf wg x

theorem right_square :
    (DoubleCylinder.map sq sq' a b c wf wg).hom.comp (Subdivision.rightEnd (e := e)).hom =
      (Subdivision.rightEnd (e := e')).hom.comp c.hom := by
  ext x
  exact DoubleCylinder.map_right sq sq' a b c wf wg x

/-- Genuine finite homotopy-cartesian gluing for the left endpoint of a
map of ordinary double mapping cylinders whose vertical maps are fibrations
and whose two edge comparisons are homotopy equivalences. -/
def leftEndHomotopyEquiv : ContinuousMap.HomotopyEquiv B
    (HomotopyPullback (DoubleCylinder.map sq sq' a b c wf wg).hom
      (Subdivision.leftEnd (e := e')).hom) :=
  HomotopyPullback.comparisonEquivOfSourceEquiv
    (DoubleCylinder.map sq sq' a b c wf wg).hom
    (NData sq' a b c wf wg).normalized.projection.hom (Subdivision.leftEnd (e := e')).hom
    b.hom (Subdivision.leftEnd (e := e)).hom (normalizedLeft sq' a b c wf wg)
    (left_square sq sq' a b c wf wg) (normalizedLeft_square sq' a b c wf wg)
    (normalizationEquiv sq sq' a b c wf wg) (normalizationEquiv_over sq sq' a b c wf wg)
    (by ext x; exact normalizationEquiv_left sq sq' a b c wf wg x)
    (normalizedLeftEndEquiv sq' a b c wf wg ha hb hc E he F hf)
    (normalizedLeftEndEquiv_toFun sq' a b c wf wg ha hb hc E he F hf)

@[simp] theorem leftEndHomotopyEquiv_toFun :
    (leftEndHomotopyEquiv sq sq' a b c wf wg ha hb hc E he F hf).toFun =
      HomotopyPullback.comparison (DoubleCylinder.map sq sq' a b c wf wg).hom
        (Subdivision.leftEnd (e := e')).hom b.hom (Subdivision.leftEnd (e := e)).hom
        (left_square sq sq' a b c wf wg) :=
  HomotopyPullback.comparisonEquivOfSourceEquiv_toFun _ _ _ _ _ _ _ _ _ _ _ _ _

/-- The matching genuine finite gluing result for the right endpoint. -/
def rightEndHomotopyEquiv : ContinuousMap.HomotopyEquiv C
    (HomotopyPullback (DoubleCylinder.map sq sq' a b c wf wg).hom
      (Subdivision.rightEnd (e := e')).hom) :=
  HomotopyPullback.comparisonEquivOfSourceEquiv
    (DoubleCylinder.map sq sq' a b c wf wg).hom
    (NData sq' a b c wf wg).normalized.projection.hom (Subdivision.rightEnd (e := e')).hom
    c.hom (Subdivision.rightEnd (e := e)).hom (normalizedRight sq' a b c wf wg)
    (right_square sq sq' a b c wf wg) (normalizedRight_square sq' a b c wf wg)
    (normalizationEquiv sq sq' a b c wf wg) (normalizationEquiv_over sq sq' a b c wf wg)
    (by ext x; exact normalizationEquiv_right sq sq' a b c wf wg x)
    (normalizedRightEndEquiv sq' a b c wf wg ha hb hc E he F hf)
    (normalizedRightEndEquiv_toFun sq' a b c wf wg ha hb hc E he F hf)

@[simp] theorem rightEndHomotopyEquiv_toFun :
    (rightEndHomotopyEquiv sq sq' a b c wf wg ha hb hc E he F hf).toFun =
      HomotopyPullback.comparison (DoubleCylinder.map sq sq' a b c wf wg).hom
        (Subdivision.rightEnd (e := e')).hom c.hom (Subdivision.rightEnd (e := e)).hom
        (right_square sq sq' a b c wf wg) :=
  HomotopyPullback.comparisonEquivOfSourceEquiv_toFun _ _ _ _ _ _ _ _ _ _ _ _ _

end TopCat.DoubleCylinder.FiniteNormalization
