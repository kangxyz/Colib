/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Category.TopCat.CompactHausdorffPushout
public import Colib.Topology.Realization.CompactGraph

/-! # Actual pushout quotients over compact realization-valued tests

These statements concern the original topological pushout and the literal
matching subspace, rather than a replaced quotient or a k-ification.


Implementation provenance:
`Quillen/Topology/Pushout/CompactParameter.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits Topology Set
open scoped Simplicial Topology
universe u v
namespace Topology
variable {A B C M : TopCat.{u}} {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ M} {j : C ⟶ M}
  (sq : IsPushout i f g j)
include sq

/-- The sum of the two actual pushout legs has the quotient topology. -/
theorem pushout_sum_isQuotientMap : IsQuotientMap (Sum.elim g j) := by
  refine isQuotientMap_iff_isClosed.mpr ⟨pushout_sum_surjective sq,?_⟩
  intro s
  constructor
  · exact fun hs ↦ hs.preimage (g.hom.continuous.sumElim j.hom.continuous)
  · intro hs
    have hB : IsClosed (g ⁻¹' s) := hs.preimage continuous_inl
    have hC : IsClosed (j ⁻¹' s) := hs.preimage continuous_inr
    rw [TopCat.isClosed_iff_of_isColimit sq.cocone sq.isColimit]
    rintro (_ | _ | _)
    · exact hB.preimage i.hom.continuous
    · exact hB
    · exact hC

/-- Pulling the actual pushout quotient back over an explicitly closed
matching locus with a locally compact parameter retains quotient topology. -/
theorem pushout_parameter_pullback_quotient_of_isClosed
    {D : Type v} [TopologicalSpace D] [LocallyCompactSpace D]
    {T : Type*} (p : M → T) (b : D → T)
    (hc : IsClosed (Set.ofPred (fun z : M × D ↦ p z.1 = b z.2))) :
    IsQuotientMap (fun z : {z : (B ⊕ C) × D // p (Sum.elim g j z.1) = b z.2} ↦
      (⟨(Sum.elim g j z.1.1,z.1.2),z.2⟩ : {z : M × D // p z.1 = b z.2})) :=
  quotientMap_parameter_pullback_of_isClosed (pushout_sum_isQuotientMap sq) p b hc

/-- In an actual realization the closed-locus condition follows from the
compact test's finite closed Hausdorff support. -/
theorem pushout_realization_parameter_pullback_quotient
    (X : SSet.{u}) {D : Type v} [TopologicalSpace D]
    [CompactSpace D] [LocallyCompactSpace D] (p : C(M, |X|)) (b : C(D, |X|)) :
    IsQuotientMap (fun z : {z : (B ⊕ C) × D // p (Sum.elim g j z.1) = b z.2} ↦
      (⟨(Sum.elim g j z.1.1,z.1.2),z.2⟩ : {z : M × D // p z.1 = b z.2})) :=
  realization_compactMap_pullback_quotient X (pushout_sum_isQuotientMap sq) p b

end Topology
