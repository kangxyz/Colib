/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.DoubleMappingCylinder.Cartesian
public import Colib.Topology.DoubleMappingCylinder.Finite.WeakCartesian
public import Colib.Topology.HomotopyFiber.CartesianTransport
public import Colib.Topology.HomotopyPullback.WeakCartesianSource

/-!
# Weakly cartesian endpoint squares of original double cylinders

Functorial mapping-path replacement converts the original weak cartesian
edge comparisons to weak strict comparisons of genuine fibrations.
Finite normalization then proves the original endpoint comparisons weak;
the genuine ordinary replacement equivalence transports them back to the
unchanged original double cylinders. No inverse of a weak edge is chosen.


Implementation provenance:
`Quillen/Topology/DoubleMappingCylinder/WeakCartesian.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section


noncomputable section
open Topology TopCat
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace TopCat.DoubleCylinder.Cartesian

variable {A B C D A' B' C' D' : TopCat.{u}}
  {f : A ⟶ B} {g : A ⟶ C} {f' : A' ⟶ B'} {g' : A' ⟶ C'}
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  {l' : A' ⊗ TopCat.I ⟶ D'} {e' : TopCat.of (B' ⊕ C') ⟶ D'}
  (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
  (sq' : IsPushout (TopCat.intervalEndpoints A') (endMap f' g') l' e')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g')
  (hgraph : ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [LocallyCompactSpace K]
    (d : C(K, D')), IsClosed (Set.ofPred (fun z : K × D' ↦ d z.1 = z.2)))
  (hL : IsWeakHomotopyEquivalence
    (HomotopyPullback.comparison b.hom f'.hom a.hom f.hom (congrArg TopCat.Hom.hom wf)))
  (hR : IsWeakHomotopyEquivalence
    (HomotopyPullback.comparison c.hom g'.hom a.hom g.hom (congrArg TopCat.Hom.hom wg)))

include hgraph in
private theorem overlap_closedGraphs
    (K : Type u) [TopologicalSpace K] [CompactSpace K] [LocallyCompactSpace K]
    (d : C(K, FiniteNormalization.Overlap sq')) :
    IsClosed (Set.ofPred (fun z : K × FiniteNormalization.Overlap sq' ↦ d z.1 = z.2)) := by
  let d' : C(K,D') := ⟨fun x ↦ (d x).val,by fun_prop⟩
  have hc := (hgraph K d').preimage
    (show Continuous (fun z : K × FiniteNormalization.Overlap sq' ↦
      (z.1,(z.2 : D'))) by fun_prop)
  convert hc using 1
  ext z
  exact Subtype.ext_iff

include hgraph hL hR in
/-- The unchanged left endpoint square is weakly cartesian when the two
original incoming edge comparisons are weakly cartesian. -/
theorem leftComparison_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence
      (HomotopyPullback.comparison (DoubleCylinder.map sq sq' a b c wf wg).hom
        (Subdivision.leftEnd (e := e')).hom b.hom (Subdivision.leftEnd (e := e)).hom
        (FiniteNormalization.left_square sq sq' a b c wf wg)) := by
  apply HomotopyPullback.comparison_isWeakHomotopyEquivalence_of_sourceMap
    (DoubleCylinder.map sq sq' a b c wf wg).hom (replacedProjection sq' a b c wf wg).hom
    (Subdivision.leftEnd (e := e')).hom b.hom (Subdivision.leftEnd (e := e)).hom
    (leftIntoReplacement a b c wf wg)
    (FiniteNormalization.left_square sq sq' a b c wf wg)
    (leftIntoReplacement_square sq' a b c wf wg)
    (replacementHomotopyEquiv sq a b c wf wg).toFun
    (isWeakHomotopyEquivalence_of_homotopyEquiv (replacementHomotopyEquiv sq a b c wf wg))
    (replacement_over sq sq' a b c wf wg)
    (by
      ext x
      exact DoubleCylinder.map_left sq (replacedSquare a b c wf wg)
        (inclusionA a) (inclusionB b) (inclusionC c)
        (inclusion_left a b wf) (inclusion_right a c wg) x)
  have hfinite := FiniteNormalization.leftEndComparison_isWeak_of_weak_edges
    (replacedSquare a b c wf wg) sq' (endpointA a) (endpointB b) (endpointC c) rfl rfl
    (MappingPath.endpoint_homotopyLiftingProperty a.hom)
    (MappingPath.endpoint_homotopyLiftingProperty b.hom)
    (MappingPath.endpoint_homotopyLiftingProperty c.hom)
    (overlap_closedGraphs sq' hgraph)
    (MappingPath.strictComparison_isWeakHomotopyEquivalence_of_comparison
      f.hom f'.hom (congrArg TopCat.Hom.hom wf) hL)
    (MappingPath.strictComparison_isWeakHomotopyEquivalence_of_comparison
      g.hom g'.hom (congrArg TopCat.Hom.hom wg) hR)
  have h := hfinite.comp
    (isWeakHomotopyEquivalence_of_homotopyEquiv (MappingPath.inclusionHomotopyEquiv b.hom))
  convert h using 1
  ext x
  rfl

include hgraph hL hR in
/-- The matching original right endpoint comparison is weak, with the
same compact graph input on the actual target double cylinder. -/
theorem rightComparison_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence
      (HomotopyPullback.comparison (DoubleCylinder.map sq sq' a b c wf wg).hom
        (Subdivision.rightEnd (e := e')).hom c.hom (Subdivision.rightEnd (e := e)).hom
        (FiniteNormalization.right_square sq sq' a b c wf wg)) := by
  apply HomotopyPullback.comparison_isWeakHomotopyEquivalence_of_sourceMap
    (DoubleCylinder.map sq sq' a b c wf wg).hom (replacedProjection sq' a b c wf wg).hom
    (Subdivision.rightEnd (e := e')).hom c.hom (Subdivision.rightEnd (e := e)).hom
    (rightIntoReplacement a b c wf wg)
    (FiniteNormalization.right_square sq sq' a b c wf wg)
    (rightIntoReplacement_square sq' a b c wf wg)
    (replacementHomotopyEquiv sq a b c wf wg).toFun
    (isWeakHomotopyEquivalence_of_homotopyEquiv (replacementHomotopyEquiv sq a b c wf wg))
    (replacement_over sq sq' a b c wf wg)
    (by
      ext x
      exact DoubleCylinder.map_right sq (replacedSquare a b c wf wg)
        (inclusionA a) (inclusionB b) (inclusionC c)
        (inclusion_left a b wf) (inclusion_right a c wg) x)
  have hfinite := FiniteNormalization.rightEndComparison_isWeak_of_weak_edges
    (replacedSquare a b c wf wg) sq' (endpointA a) (endpointB b) (endpointC c) rfl rfl
    (MappingPath.endpoint_homotopyLiftingProperty a.hom)
    (MappingPath.endpoint_homotopyLiftingProperty b.hom)
    (MappingPath.endpoint_homotopyLiftingProperty c.hom)
    (overlap_closedGraphs sq' hgraph)
    (MappingPath.strictComparison_isWeakHomotopyEquivalence_of_comparison
      f.hom f'.hom (congrArg TopCat.Hom.hom wf) hL)
    (MappingPath.strictComparison_isWeakHomotopyEquivalence_of_comparison
      g.hom g'.hom (congrArg TopCat.Hom.hom wg) hR)
  have h := hfinite.comp
    (isWeakHomotopyEquivalence_of_homotopyEquiv (MappingPath.inclusionHomotopyEquiv c.hom))
  convert h using 1
  ext x
  rfl

end TopCat.DoubleCylinder.Cartesian
