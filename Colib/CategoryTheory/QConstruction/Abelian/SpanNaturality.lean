/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.QConstruction.Abelian.CospanComposition

/-!
# Naturality of abelian Q-spans under cartesian maps

The actual mono and reversed-epi Q-arrows satisfy the displayed naturality
identities. Adapted from `Quillen/Localization/Serre/AuxiliaryBaseChange.lean`
and `AuxiliaryStructuredTransition.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, with independent object and
morphism universes and no localization hypotheses.
-/

@[expose] public noncomputable section

universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.QConstruction
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A cartesian map on left legs and a commuting map on right legs gives
naturality of the associated Q-spans. -/
theorem span_naturality_of_pullback {X Y X' Y' : C}
    (s : AbelianSpan X Y) (t : AbelianSpan X' Y')
    (a : X ⟶ X') (b : Y ⟶ Y') (c : s.apex ⟶ t.apex)
    [Mono a] [Mono b]
    (sq : IsPullback s.l c a t.l) (hr : s.r ≫ b = c ≫ t.r) :
    mkHom _ _ s ≫ inflationArrow b = inflationArrow a ≫ mkHom _ _ t := by
  let sq₁ : IsPullback (𝟙 s.apex) s.r s.r (𝟙 Y) := IsPullback.of_id_fst
  apply mkHom_eq_of_apexIso _ _ _ _ (sq₁.isoPullback.symm ≪≫ sq.isoPullback)
  · change (sq₁.isoPullback.inv ≫ sq.isoPullback.hom) ≫
        pullback.fst a t.l ≫ 𝟙 X = pullback.fst s.r (𝟙 Y) ≫ s.l
    simp only [Category.assoc, Category.comp_id, IsPullback.isoPullback_hom_fst]
    have h : sq₁.isoPullback.inv = pullback.fst s.r (𝟙 Y) := by
      simpa using sq₁.isoPullback_inv_fst
    rw [h]
  · change (sq₁.isoPullback.inv ≫ sq.isoPullback.hom) ≫
        pullback.snd a t.l ≫ t.r = pullback.snd s.r (𝟙 Y) ≫ b
    simp only [Category.assoc, IsPullback.isoPullback_hom_snd_assoc]
    rw [← hr, ← Category.assoc]
    have h : sq₁.isoPullback.inv ≫ s.r = pullback.snd s.r (𝟙 Y) :=
      sq₁.isoPullback_inv_snd
    rw [h]

/-- The reversed arrow of an ordinary isomorphism is its inverse Q-isomorphism. -/
lemma surjectionArrow_eq_qIsoOfIso_inv {X Y : C} (e : X ≅ Y) :
    surjectionArrow e.hom = ((abelianExactStructure C).qIsoOfIso e).inv := by
  apply mkHom_eq_of_apexIso _ _ _ _ e
  · simp [QConstruction.isoSpan]
  · simp [QConstruction.isoSpan]

/-- The epi version of span naturality uses a cartesian square on right legs. -/
theorem span_naturality_of_surjection_pullback {X Y X' Y' : C}
    (s : AbelianSpan X Y) (t : AbelianSpan X' Y')
    (a : X' ⟶ X) (b : Y' ⟶ Y) (c : t.apex ⟶ s.apex)
    [Epi a] [Epi b]
    (hl : t.l ≫ a = c ≫ s.l) (sq : IsPullback t.r c b s.r) :
    mkHom _ _ s ≫ surjectionArrow b = surjectionArrow a ≫ mkHom _ _ t := by
  let sq₁ : IsPullback t.l (𝟙 t.apex) (𝟙 X') t.l := IsPullback.of_vert_isIso ⟨by simp⟩
  apply mkHom_eq_of_apexIso _ _ _ _ (sq.flip.isoPullback.symm ≪≫ sq₁.isoPullback)
  · change (sq.flip.isoPullback.inv ≫ sq₁.isoPullback.hom) ≫
        pullback.fst (𝟙 X') t.l ≫ a = pullback.fst s.r b ≫ s.l
    simp only [Category.assoc, IsPullback.isoPullback_hom_fst_assoc]
    rw [hl, ← Category.assoc]
    exact congrArg (· ≫ s.l) sq.flip.isoPullback_inv_fst
  · change (sq.flip.isoPullback.inv ≫ sq₁.isoPullback.hom) ≫
        pullback.snd (𝟙 X') t.l ≫ t.r = pullback.snd s.r b ≫ 𝟙 Y'
    simp only [Category.assoc, IsPullback.isoPullback_hom_snd_assoc,
      Category.id_comp, Category.comp_id]
    exact sq.flip.isoPullback_inv_snd

end CategoryTheory.QConstruction
