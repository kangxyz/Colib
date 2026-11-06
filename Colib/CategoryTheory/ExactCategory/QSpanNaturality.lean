/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.QIsomorphisms

/-! # Compatible endpoint and apex isomorphisms give actual Q naturality

Adapted from `Quillen/CategoryTheory/QConstruction/SpanIsoNaturality.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original span representatives.
-/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C)

/-- A commuting isomorphism of span diagrams gives the corresponding naturality
square in the original Q category, with its original pullback composition. -/
theorem qSpan_iso_naturality {X Y X' Y' : C}
    (s : Span E.deflation E.inflation X Y) (t : Span E.deflation E.inflation X' Y')
    (eX : X ≅ X') (eY : Y ≅ Y') (eA : s.apex ≅ t.apex)
    (hl : s.l ≫ eX.hom = eA.hom ≫ t.l) (hr : s.r ≫ eY.hom = eA.hom ≫ t.r) :
    QConstruction.mkHom _ _ s ≫ (E.qIsoOfIso eY).hom =
      (E.qIsoOfIso eX).hom ≫ QConstruction.mkHom _ _ t := by
  let u : Span E.deflation E.inflation X Y' :=
    ⟨s.apex, s.l, s.r ≫ eY.hom, s.wl,
      E.inflation_comp _ _ s.wr (E.inflation_of_iso eY)⟩
  let sq₁ : IsPullback (𝟙 s.apex) s.r s.r (𝟙 Y) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  let sq₂ : IsPullback s.l eA.hom eX.hom t.l :=
    IsPullback.of_vert_isIso ⟨hl⟩
  let : HasPullback s.r (𝟙 Y) := sq₁.hasPullback
  let : HasPullback eX.hom t.l := sq₂.hasPullback
  have h₁ : QConstruction.mkHom _ _ u = QConstruction.mkHom _ _ s ≫ (E.qIsoOfIso eY).hom := by
    apply QConstruction.mkHom_eq_of_apexIso _ _ _ _ sq₁.isoPullback
    · change sq₁.isoPullback.hom ≫ pullback.fst _ _ ≫ s.l = s.l
      simp
    · change sq₁.isoPullback.hom ≫ pullback.snd _ _ ≫ eY.hom = s.r ≫ eY.hom
      simp
  have h₂ : QConstruction.mkHom _ _ u = (E.qIsoOfIso eX).hom ≫ QConstruction.mkHom _ _ t := by
    apply QConstruction.mkHom_eq_of_apexIso _ _ _ _ sq₂.isoPullback
    · change sq₂.isoPullback.hom ≫ pullback.fst _ _ ≫ 𝟙 _ = s.l
      simp
    · change sq₂.isoPullback.hom ≫ pullback.snd _ _ ≫ t.r = s.r ≫ eY.hom
      simpa only [IsPullback.isoPullback_hom_snd_assoc] using hr.symm
  exact h₁.symm.trans h₂

end CategoryTheory.ExactCategory.ExactStructure
