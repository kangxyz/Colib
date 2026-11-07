/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Pushout.Open.Embedding

/-!
# Attaching along an actual open subspace

The other corner embeds openly even when its attaching map is arbitrary.
When the attaching subspace is precisely the inverse image of an open base
set, its pushout chart is exactly that base restriction. This is the local
chart calculation for the normalized finite homotopy-cartesian cube.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/Pushout/Open/Attachment.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual maps and hypotheses. -/
@[expose] public section

noncomputable section
open CategoryTheory Limits Topology
open scoped Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace TopCat
variable {A B C D : TopCat.{u}} {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}

/-- Pushing out one open embedding preserves that open embedding. The
opposite attaching map is arbitrary, and need not be injective. -/
theorem pushout_inl_isOpenEmbedding_of_right (sq : IsPushout i f g j)
    (hf : IsOpenEmbedding f) : IsOpenEmbedding g := by
  let sqT := sq.map (forget TopCat)
  have hg : Function.Injective g :=
    Types.pushoutCocone_inr_injective_of_isColimit sqT.flip.isColimit hf.injective
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap g.hom.continuous hg
  intro W hW
  have hl : g ⁻¹' (g '' W) = W := Set.preimage_image_eq _ hg
  have hr : j ⁻¹' (g '' W) = f '' (i ⁻¹' W) := by
    ext c
    constructor
    · rintro ⟨b, hb, hbc⟩
      obtain ⟨a, hac, hab⟩ :=
        (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
          sqT.flip.isColimit hf.injective c b).mp hbc.symm
      change f a = c at hac
      change i a = b at hab
      refine ⟨a, ?_, hac⟩
      change i a ∈ W
      rw [hab]
      exact hb
    · rintro ⟨a, ha, rfl⟩
      exact ⟨i a, ha, ConcreteCategory.congr_hom sq.w a⟩
  rw [TopCat.isOpen_iff_of_isColimit sq.cocone sq.isColimit]
  rintro (_ | _ | _)
  · change IsOpen (i ⁻¹' (g ⁻¹' (g '' W)))
    rw [hl]
    exact hW.preimage i.hom.continuous
  · change IsOpen (g ⁻¹' (g '' W))
    rw [hl]
    exact hW
  · change IsOpen (j ⁻¹' (g '' W))
    rw [hr]
    exact hf.isOpenMap _ (hW.preimage i.hom.continuous)

theorem pushout_inr_isOpenEmbedding_of_left (sq : IsPushout i f g j)
    (hi : IsOpenEmbedding i) : IsOpenEmbedding j :=
  pushout_inl_isOpenEmbedding_of_right sq.flip hi

namespace OpenAttachment
variable {B C D T : TopCat.{u}} (pC : C ⟶ T) (U : Set T)

/-- Include the inverse image of the base subset `U` under `pC` into the original corner `C`, as
the attaching leg for an open-subspace pushout. -/
def inclusion : TopCat.of {c : C // pC c ∈ U} ⟶ C :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

variable {i : TopCat.of {c : C // pC c ∈ U} ⟶ B}
  {g : B ⟶ D} {j : C ⟶ D}
  (sq : IsPushout i (inclusion pC U) g j)
  (p : D ⟶ T) (hj : j ≫ p = pC) (hB : ∀ b, p (g b) ∈ U)

include sq hj hB in
/-- The remaining chart is exactly the preimage of the chosen open base
set after the attachment, including the existing subspace topology. -/
theorem range_eq_preimage : Set.range g = p ⁻¹' U := by
  ext d
  constructor
  · rintro ⟨b, rfl⟩
    exact hB b
  · intro hd
    rcases Types.eq_or_eq_of_isPushout (sq.map (forget TopCat)) d with ⟨b, hb⟩ | ⟨c, hc⟩
    · exact ⟨b, hb⟩
    · change j c = d at hc
      have hu : pC c ∈ U := by
        rw [← ConcreteCategory.congr_hom hj c]
        change p (j c) ∈ U
        rw [hc]
        exact hd
      exact ⟨i ⟨c, hu⟩, (ConcreteCategory.congr_hom sq.w ⟨c, hu⟩).trans hc⟩

/-- Canonical map into the restricted total space. -/
def chartMap : C(B, {d : D // p d ∈ U}) := ⟨fun b ↦ ⟨g b, hB b⟩, by fun_prop⟩

/-- Attaching precisely the complementary chart gives an actual
homeomorphism from the unchanged piece onto its base restriction. -/
def chartHomeomorph (hU : IsOpen U) : B ≃ₜ {d : D // p d ∈ U} := by
  have hg : IsOpenEmbedding g := pushout_inl_isOpenEmbedding_of_right sq
    ((hU.preimage pC.hom.continuous).isOpenEmbedding_subtypeVal)
  have he : IsEmbedding (chartMap U p hB) :=
    IsEmbedding.subtypeVal.of_comp_iff.mp hg.isEmbedding
  apply he.toHomeomorphOfSurjective
  intro d
  have hd : d.1 ∈ Set.range g := by
    rw [range_eq_preimage pC U sq p hj hB]
    exact d.2
  obtain ⟨b, hb⟩ := hd
  exact ⟨b, Subtype.ext hb⟩

@[simp] theorem chartHomeomorph_apply (hU : IsOpen U) (b : B) :
    (chartHomeomorph pC U sq p hj hB hU b).1 = g b := rfl

end OpenAttachment
end TopCat
