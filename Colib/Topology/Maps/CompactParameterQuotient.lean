/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.WithTopology
public import Mathlib.Topology.Separation.Hausdorff

/-! # Quotient descent over an actual locally compact parameter

Products by a locally compact parameter preserve quotient maps. Restriction
to a closed matching locus then gives the actual pullback quotient needed
for finite parametrized mapping-cylinder formulas. No arbitrary-product
or arbitrary-pullback preservation is used.


Implementation provenance:
`Quillen/Topology/Maps/CompactParameterQuotient.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology
open Topology Set
universe u v w z
namespace Topology

/-- Restriction of an actual quotient to a closed target subset is quotient. -/
theorem quotientMap_restrictPreimage_isClosed
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsQuotientMap f) {s : Set Y} (hs : IsClosed s) :
    IsQuotientMap (s.restrictPreimage f) := by
  refine (isQuotientMap_iff _).2 ⟨?_,hf.surjective.restrictPreimage _⟩
  refine .of_isClosed_preimage_iff_isClosed fun t ↦ ?_
  rw [hs.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed,
    ← hf.isCoinducing.isClosed_preimage,
    (hs.preimage hf.continuous).isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed,
    image_val_preimage_restrictPreimage]

/-- The literal quotient product map is quotient for a locally compact
parameter; no separation assumptions are needed here. -/
theorem quotientMap_prod_parameter
    {X : Type u} {Y : Type v} {D : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace D]
    [LocallyCompactSpace D] {f : X → Y} (hf : IsQuotientMap f) :
    IsQuotientMap (fun z : X × D ↦ (f z.1,z.2)) := by
  let original : TopologicalSpace (Y × D) := inferInstance
  let τ := TopologicalSpace.coinduced (fun z : X × D ↦ (f z.1,z.2)) inferInstance
  let : TopologicalSpace (Y × D) := original
  have hcont : Continuous (fun y : Y × D ↦ WithTopology.toTopology τ y) :=
    hf.continuous_lift_prod_left
      ⟨fun s hs ↦ hs⟩
  refine ⟨⟨le_antisymm ?_ ((hf.continuous.prodMap continuous_id).coinduced_le)⟩,?_⟩
  · change ∀ s, τ.IsOpen s → original.IsOpen s
    intro s hs
    exact hcont.isOpen_preimage (WithTopology.ofTopology ⁻¹' s) hs
  · rintro ⟨y,d⟩
    obtain ⟨x,rfl⟩ := hf.surjective y
    exact ⟨(x,d),rfl⟩

/-- An explicitly closed matching locus suffices for the literal pullback
of a quotient along a locally compact test parameter. -/
theorem quotientMap_parameter_pullback_of_isClosed
    {X : Type u} {Y : Type v} {D : Type w} {T : Type z}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace D]
    [LocallyCompactSpace D] {f : X → Y} (hf : IsQuotientMap f)
    (p : Y → T) (b : D → T) (hclosed : IsClosed {z : Y × D | p z.1 = b z.2}) :
    IsQuotientMap (fun z : {z : X × D // p (f z.1) = b z.2} ↦
      (⟨(f z.1.1,z.1.2),z.2⟩ : {z : Y × D // p z.1 = b z.2})) :=
  quotientMap_restrictPreimage_isClosed (quotientMap_prod_parameter hf) hclosed

/-- A closed graph of the displayed test map suffices; global separation of
its codomain is unnecessary. -/
theorem quotientMap_parameter_pullback_of_closedGraph
    {X : Type u} {Y : Type v} {D : Type w} {T : Type z}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace D]
    [TopologicalSpace T] [LocallyCompactSpace D]
    {f : X → Y} (hf : IsQuotientMap f) (p : C(Y, T)) (b : C(D, T))
    (hb : IsClosed (Set.ofPred (fun z : D × T ↦ b z.1 = z.2))) :
    IsQuotientMap (fun z : {z : X × D // p (f z.1) = b z.2} ↦
      (⟨(f z.1.1,z.1.2),z.2⟩ : {z : Y × D // p z.1 = b z.2})) := by
  apply quotientMap_parameter_pullback_of_isClosed hf p b
  have hc := hb.preimage (continuous_snd.prodMk (p.continuous.comp continuous_fst))
  convert hc using 1
  ext z
  exact eq_comm

/-- Hausdorffness of the base is one sufficient, explicit matching-locus
condition for finite-parameter pullback descent. -/
theorem quotientMap_parameter_pullback
    {X : Type u} {Y : Type v} {D : Type w} {T : Type z}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace D]
    [TopologicalSpace T] [T2Space T] [LocallyCompactSpace D]
    {f : X → Y} (hf : IsQuotientMap f) (p : C(Y, T)) (b : C(D, T)) :
    IsQuotientMap (fun z : {z : X × D // p (f z.1) = b z.2} ↦
      (⟨(f z.1.1,z.1.2),z.2⟩ : {z : Y × D // p z.1 = b z.2})) :=
  quotientMap_parameter_pullback_of_isClosed hf p b
    (isClosed_eq (p.continuous.comp continuous_fst) (b.continuous.comp continuous_snd))

end Topology
