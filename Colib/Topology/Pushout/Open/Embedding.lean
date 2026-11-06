/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Pushout.Open.Restriction

/-! Gluing along two actual open embeddings gives an actual open-union
pushout, with no unsupported arbitrary quotient base-change assertion. -/
/-! Implementation provenance: adapted from
`Quillen/Topology/Pushout/Open/Embedding.lean` at
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
  (sq : IsPushout i f g j)
include sq

/-- The left pushout inclusion is open embedding when both attaching legs are. -/
theorem pushout_inl_isOpenEmbedding (hi : IsOpenEmbedding i) (hf : IsOpenEmbedding f) :
    IsOpenEmbedding g := by
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
      obtain ⟨a, hab, hac⟩ :=
        (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit sqT.isColimit hi.injective b c).mp hbc
      change i a = b at hab
      change f a = c at hac
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

/-- Both maps into the glued space are open embeddings. -/
theorem pushout_inr_isOpenEmbedding (hi : IsOpenEmbedding i) (hf : IsOpenEmbedding f) :
    IsOpenEmbedding j := pushout_inl_isOpenEmbedding sq.flip hf hi

/-- The two open images actually cover the entire pushout. -/
theorem pushout_open_union (hi : IsOpenEmbedding i) (hf : IsOpenEmbedding f) :
    IsOpen (Set.range g) ∧ IsOpen (Set.range j) ∧ Set.range g ∪ Set.range j = Set.univ := by
  refine ⟨(pushout_inl_isOpenEmbedding sq hi hf).isOpen_range,
    (pushout_inr_isOpenEmbedding sq hi hf).isOpen_range, ?_⟩
  apply Set.eq_univ_iff_forall.mpr
  intro d
  exact Types.eq_or_eq_of_isPushout (sq.map (forget TopCat)) d

end TopCat
