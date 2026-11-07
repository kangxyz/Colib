/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.FiniteHausdorff
public import Colib.Topology.Realization.FiniteSubcomplex
public import Colib.Topology.Maps.CompactParameterQuotient

/-! # Closed graphs of compact tests in actual simplicial realizations

The actual map factors through a finite realized subcomplex, whose inclusion
is a closed embedding and whose realization is Hausdorff. This gives the
closed matching locus needed for quotient descent without assuming the
entire realization Hausdorff.


Implementation provenance:
`Quillen/Topology/Realization/CompactGraph.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat SSet
open CategoryTheory Topology Set
open scoped Simplicial Topology
universe u v w z
namespace Topology

/-- Every compact-source map into the unchanged actual realization has
closed graph, by its finite closed Hausdorff support. -/
theorem realization_compactMap_isClosed_graph (X : SSet.{u})
    {D : Type v} [TopologicalSpace D] [CompactSpace D] (b : C(D, |X|)) :
    IsClosed (Set.ofPred (fun z : D × |X| ↦ b z.1 = z.2)) := by
  obtain ⟨A,hA,g,hg⟩ := realization_continuousMap_factors_finiteSubcomplex b
  let : SSet.Finite (A : SSet.{u}) := hA
  have he := (IsClosedEmbedding.id (X := D)).prodMap
    (realization_mono_isClosedEmbedding A.ι)
  have hc := he.isClosedMap _ (isClosed_eq (g.continuous.comp continuous_fst) continuous_snd)
  convert hc using 1
  ext z
  constructor
  · intro hz
    exact ⟨(z.1,g z.1),rfl,Prod.ext rfl
      ((ContinuousMap.congr_fun hg z.1).trans hz)⟩
  · rintro ⟨⟨d,a⟩,ha,hz⟩
    cases hz
    exact (ContinuousMap.congr_fun hg d).symm.trans (congrArg (SSet.toTop.map A.ι) ha)

/-- Matching an arbitrary continuous base projection against a compact test
in a realization is a closed condition in the original product topology. -/
theorem realization_compactMap_matching_isClosed (X : SSet.{u})
    {Y : Type w} {D : Type v} [TopologicalSpace Y] [TopologicalSpace D]
    [CompactSpace D] (p : C(Y, |X|)) (b : C(D, |X|)) :
    IsClosed (Set.ofPred (fun z : Y × D ↦ p z.1 = b z.2)) := by
  have hc := (realization_compactMap_isClosed_graph X b).preimage
    (continuous_snd.prodMk (p.continuous.comp continuous_fst))
  convert hc using 1
  ext z
  exact eq_comm

/-- The original quotient remains quotient after pullback over a compact
locally compact test in an actual realization. -/
theorem realization_compactMap_pullback_quotient (X : SSet.{u})
    {E : Type z} {Y : Type w} {D : Type v}
    [TopologicalSpace E] [TopologicalSpace Y] [TopologicalSpace D]
    [CompactSpace D] [LocallyCompactSpace D] {q : E → Y} (hq : IsQuotientMap q)
    (p : C(Y, |X|)) (b : C(D, |X|)) :
    IsQuotientMap (fun z : {z : E × D // p (q z.1) = b z.2} ↦
      (⟨(q z.1.1,z.1.2),z.2⟩ : {z : Y × D // p z.1 = b z.2})) :=
  quotientMap_parameter_pullback_of_isClosed hq p b
    (realization_compactMap_matching_isClosed X p b)

end Topology
