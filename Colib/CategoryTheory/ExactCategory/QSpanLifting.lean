/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.QSpanNaturality

/-! # Lifting Q-naturality to the unique apex isomorphism

Equality in Q is exactly equality up to an isomorphism of actual admissible
span apices. Commuting endpoint isomorphisms therefore lift uniquely to the
span representatives; no quotient relation beyond apex isomorphism is used.
-/
/- Adapted from the corresponding Quillen Q/S reconstruction source at
   c561118b7795eb9780be9ed391c3251d6a4d0afd. Native Colib objects are retained. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe v u

namespace CategoryTheory.ExactCategory.ExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : CategoryTheory.ExactCategory.ExactStructure C)

/-- A commuting Q-square with invertible endpoints lifts to an apex isomorphism. -/
theorem exists_apexIso_of_q_naturality {X Y X' Y' : C}
    (s : Span E.deflation E.inflation X Y) (t : Span E.deflation E.inflation X' Y')
    (a : X ≅ X') (b : Y ≅ Y')
    (h : QConstruction.mkHom E.deflation E.inflation s ≫ (E.qIsoOfIso b).hom =
      (E.qIsoOfIso a).hom ≫ QConstruction.mkHom E.deflation E.inflation t) :
    ∃ c : s.apex ≅ t.apex, s.l ≫ a.hom = c.hom ≫ t.l ∧ s.r ≫ b.hom = c.hom ≫ t.r := by
  let u : Span E.deflation E.inflation X Y' :=
    { apex := s.apex
      l := s.l
      r := s.r ≫ b.hom
      wl := s.wl
      wr := E.inflation_comp _ _ s.wr (E.inflation_of_iso b) }
  let v : Span E.deflation E.inflation X Y' :=
    { apex := t.apex
      l := t.l ≫ a.inv
      r := t.r
      wl := E.deflation_comp _ _ t.wl (E.deflation_of_iso a.symm)
      wr := t.wr }
  have hu : QConstruction.mkHom E.deflation E.inflation u =
      QConstruction.mkHom E.deflation E.inflation s ≫ (E.qIsoOfIso b).hom := by
    have he := E.qSpan_iso_naturality s u (Iso.refl X) b (Iso.refl s.apex)
      (by simp [u]) (by simp [u])
    simpa using he.symm
  have hv : QConstruction.mkHom E.deflation E.inflation v =
      (E.qIsoOfIso a).hom ≫ QConstruction.mkHom E.deflation E.inflation t := by
    have he := E.qSpan_iso_naturality v t a (Iso.refl Y') (Iso.refl t.apex)
      (by simp [v]) (by simp [v])
    simpa using he
  have huv : QConstruction.mkHom E.deflation E.inflation u = QConstruction.mkHom E.deflation
    E.inflation v :=
    hu.trans (h.trans hv.symm)
  obtain ⟨c, hl, hr⟩ := (QConstruction.mkHom_eq_iff_apexIso _ _ u v).mp huv
  refine ⟨c, ?_, hr.symm⟩
  have hla := congrArg (fun f ↦ f ≫ a.hom) hl
  simpa only [v, u, Category.assoc, Iso.inv_hom_id, Category.comp_id] using hla.symm

/-- The lift is unique because an admissible monomorphism is monic. -/
theorem apexIso_unique_of_right {X Y X' Y' : C}
    (s : Span E.deflation E.inflation X Y) (t : Span E.deflation E.inflation X' Y')
    (b : Y ≅ Y') (c d : s.apex ≅ t.apex)
    (hc : s.r ≫ b.hom = c.hom ≫ t.r) (hd : s.r ≫ b.hom = d.hom ≫ t.r) : c = d := by
  let : Mono t.r := E.mono_of_inflation t.wr
  apply Iso.ext
  exact (cancel_mono t.r).mp (hc.symm.trans hd)

/-- Every commuting invertible-endpoint Q-square has exactly one actual
commuting apex isomorphism. -/
theorem existsUnique_apexIso_of_q_naturality {X Y X' Y' : C}
    (s : Span E.deflation E.inflation X Y) (t : Span E.deflation E.inflation X' Y')
    (a : X ≅ X') (b : Y ≅ Y')
    (h : QConstruction.mkHom E.deflation E.inflation s ≫ (E.qIsoOfIso b).hom =
      (E.qIsoOfIso a).hom ≫ QConstruction.mkHom E.deflation E.inflation t) :
    ∃! c : s.apex ≅ t.apex, s.l ≫ a.hom = c.hom ≫ t.l ∧ s.r ≫ b.hom = c.hom ≫ t.r := by
  obtain ⟨c, hl, hr⟩ := exists_apexIso_of_q_naturality E s t a b h
  exact ⟨c, ⟨hl, hr⟩, fun d hd ↦ apexIso_unique_of_right E s t b d c hd.2 hr⟩

end CategoryTheory.ExactCategory.ExactStructure
