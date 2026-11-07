/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.DoubleCylinder
public import Colib.Topology.Realization.CompactGraph

/-!
# Compact test graphs in an actual simplicial double-cylinder model

The actual homeomorphism, rather than a homotopy equivalence, transports
closed graphs and the finite-parameter quotient pullback topology.


Implementation provenance:
`Quillen/Topology/Realization/DoubleCylinderCompactGraph.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open Topology

noncomputable section
open Topology TopCat SSet
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology
universe u v w z
namespace TopCat.DoubleCylinder
variable {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ Z)
  {T : TopCat.{u}} {l : |X| ⊗ TopCat.I ⟶ T} {e : TopCat.of (|Y| ⊕ |Z|) ⟶ T}
  (sq : IsPushout (TopCat.intervalEndpoints |X|)
    (endMap (SSet.toTop.map f) (SSet.toTop.map g)) l e)

include f g sq

/-- Every compact test in the unchanged displayed double cylinder has closed graph. -/
theorem compactMap_isClosed_graph
    {D : Type v} [TopologicalSpace D] [CompactSpace D] (b : C(D, T)) :
    IsClosed (Set.ofPred (fun z : D × T ↦ b z.1 = z.2)) := by
  let h := realizationHomeomorph f g sq
  let b' : C(D,|simplicial f g|) := (h.symm : C(T,|simplicial f g|)).comp b
  have hc := (realization_compactMap_isClosed_graph (simplicial f g) b').preimage
    (continuous_id.prodMap h.symm.continuous)
  convert hc using 1
  ext z
  exact h.symm.injective.eq_iff.symm

/-- An arbitrary projection matched against a compact base test defines a closed locus. -/
theorem compactMap_matching_isClosed
    {P : Type w} {D : Type v} [TopologicalSpace P] [TopologicalSpace D]
    [CompactSpace D] (p : C(P, T)) (b : C(D, T)) :
    IsClosed (Set.ofPred (fun z : P × D ↦ p z.1 = b z.2)) := by
  have hc := (compactMap_isClosed_graph f g sq b).preimage
    (continuous_snd.prodMk (p.continuous.comp continuous_fst))
  convert hc using 1
  ext z
  exact eq_comm

/-- The literal quotient pullback is quotient for a compact locally compact
parameter in the actual displayed double-cylinder base. -/
theorem compactMap_pullback_quotient
    {E : Type z} {P : Type w} {D : Type v}
    [TopologicalSpace E] [TopologicalSpace P] [TopologicalSpace D]
    [CompactSpace D] [LocallyCompactSpace D] {q : E → P} (hq : IsQuotientMap q)
    (p : C(P, T)) (b : C(D, T)) :
    IsQuotientMap (fun z : {z : E × D // p (q z.1) = b z.2} ↦
      (⟨(q z.1.1,z.1.2),z.2⟩ : {z : P × D // p z.1 = b z.2})) :=
  quotientMap_parameter_pullback_of_closedGraph hq p b (compactMap_isClosed_graph f g sq b)

end TopCat.DoubleCylinder
