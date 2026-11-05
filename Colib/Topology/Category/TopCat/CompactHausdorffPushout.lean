/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Category.TopCat.PushoutInteriors
public import Mathlib.Topology.Separation.Hausdorff

/-! # Compact Hausdorff topological pushouts along closed embeddings

The displayed pushout retains its actual TopCat colimit topology. Its cell leg
is closed: saturation of a closed cell subset consists of that subset and the
closed attaching locus over the compact image of its boundary part. The sum of
the two legs is therefore a closed surjection from a compact Hausdorff space.
Separating its compact fibers proves the actual pushout Hausdorff.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Topology Set
universe u v

namespace TopCat

/-- A closed continuous surjection from a compact Hausdorff space to a T₁
space has Hausdorff codomain. Disjoint compact fibers admit disjoint open
neighborhoods, whose closed-image complements descend to the codomain. -/
theorem t2Space_of_closed_surjection {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space X] [T1Space Y]
    {q : X → Y} (hq : Continuous q) (hs : Function.Surjective q)
    (hc : IsClosedMap q) : T2Space Y := by
  constructor
  intro x y hxy
  have hx : IsCompact (q ⁻¹' {x}) := (isClosed_singleton.preimage hq).isCompact
  have hy : IsCompact (q ⁻¹' {y}) := (isClosed_singleton.preimage hq).isCompact
  have hd : Disjoint (q ⁻¹' {x}) (q ⁻¹' {y}) := by
    rw [Set.disjoint_left]
    intro a hax hay
    exact hxy (hax.symm.trans hay)
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ :=
    SeparatedNhds.of_isCompact_isCompact hx hy hd
  refine ⟨(q '' Uᶜ)ᶜ, (q '' Vᶜ)ᶜ,
    (hc _ hU.isClosed_compl).isOpen_compl, (hc _ hV.isClosed_compl).isOpen_compl,
    ?_, ?_, ?_⟩
  · rintro ⟨a, ha, hax⟩
    exact ha (hxU hax)
  · rintro ⟨a, ha, hay⟩
    exact ha (hyV hay)
  · rw [Set.disjoint_left]
    intro z hzU hzV
    obtain ⟨a, rfl⟩ := hs z
    have haU : a ∈ U := by
      by_contra ha
      exact hzU ⟨a, ha, rfl⟩
    have haV : a ∈ V := by
      by_contra ha
      exact hzV ⟨a, ha, rfl⟩
    exact Set.disjoint_left.mp hUV haU haV

section Pushout
variable {A B C D : TopCat.{u}} {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    (sq : IsPushout i f g j)

include sq

/-- The two original topological pushout legs are jointly surjective. -/
theorem pushout_sum_surjective : Function.Surjective (Sum.elim g j) := by
  intro z
  rcases Types.eq_or_eq_of_isPushout (sq.map (forget TopCat)) z with ⟨b, hb⟩ | ⟨c, hc⟩
  · exact ⟨Sum.inl b, hb⟩
  · exact ⟨Sum.inr c, hc⟩

/-- Compactness of a genuine pushout follows from compactness of its two
outgoing objects, with no separation or embedding hypothesis. -/
theorem compactSpace_pushout [CompactSpace B] [CompactSpace C] : CompactSpace D :=
  Function.Surjective.compactSpace (g.hom.continuous.sumElim j.hom.continuous)
    (pushout_sum_surjective sq)

/-- The cell leg of a pushout along a closed embedding with compact source
and Hausdorff old space is a closed map. -/
theorem isClosedMap_pushout_left_of_compact [CompactSpace A] [T2Space C]
    (hi : IsClosedEmbedding i) : IsClosedMap g := by
  intro W hW
  let sqT := sq.map (forget TopCat)
  have hright : j ⁻¹' (g '' W) = f '' (i ⁻¹' W) := by
    ext c
    constructor
    · rintro ⟨b, hb, hbc⟩
      obtain ⟨a, hab, hac⟩ :=
        (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit sqT.isColimit
          hi.injective b c).mp hbc
      change i a = b at hab
      change f a = c at hac
      exact ⟨a, by change i a ∈ W; rwa [hab], hac⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨i a, ha, ConcreteCategory.congr_hom sq.w a⟩
  have hleft : g ⁻¹' (g '' W) = W ∪ i '' (f ⁻¹' (f '' (i ⁻¹' W))) := by
    ext b
    constructor
    · rintro ⟨b', hb', hbb'⟩
      by_cases hb : b ∈ Set.range i
      · obtain ⟨a, rfl⟩ := hb
        right
        refine ⟨a, ?_, rfl⟩
        change f a ∈ f '' (i ⁻¹' W)
        rw [← hright]
        exact ⟨b', hb', hbb'.trans (ConcreteCategory.congr_hom sq.w a)⟩
      · left
        exact (pushout_cell_eq_of_not_mem_range sq hb hbb'.symm) ▸ hb'
    · rintro (hb | ⟨a, ha, rfl⟩)
      · exact ⟨b, hb, rfl⟩
      · change f a ∈ f '' (i ⁻¹' W) at ha
        rw [← hright] at ha
        obtain ⟨b', hb', he⟩ := ha
        exact ⟨b', hb', he.trans (ConcreteCategory.congr_hom sq.w a).symm⟩
  have hclosed : IsClosed (f '' (i ⁻¹' W)) :=
    ((hW.preimage i.hom.continuous).isCompact.image f.hom.continuous).isClosed
  have hclosedLeft : IsClosed (g ⁻¹' (g '' W)) := by
    rw [hleft]
    exact hW.union (hi.isClosedMap _ (hclosed.preimage f.hom.continuous))
  rw [TopCat.isClosed_iff_of_isColimit sq.cocone sq.isColimit]
  rintro (_ | _ | _)
  · exact hclosedLeft.preimage i.hom.continuous
  · exact hclosedLeft
  · change IsClosed (j ⁻¹' (g '' W))
    rwa [hright]

/-- A genuine pushout of compact Hausdorff spaces along a closed embedding
is Hausdorff. Compactness of the attaching object is derived from the embedding. -/
theorem t2Space_pushout_of_compact_closedEmbedding
    [CompactSpace B] [T2Space B] [CompactSpace C] [T2Space C]
    (hi : IsClosedEmbedding i) : T2Space D := by
  let : CompactSpace A := hi.compactSpace
  let : T1Space D := t1Space_pushout_of_closedEmbedding sq hi
  exact t2Space_of_closed_surjection (g.hom.continuous.sumElim j.hom.continuous)
    (pushout_sum_surjective sq)
    ((isClosedMap_pushout_left_of_compact sq hi).sumElim
      (isClosedEmbedding_pushout_right sq hi).isClosedMap)

end Pushout
end TopCat
