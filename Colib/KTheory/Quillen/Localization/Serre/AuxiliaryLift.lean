/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Abelian.SerreClass.Lifts
public import Colib.KTheory.Quillen.Localization.Serre.Basic
public import Colib.CategoryTheory.Abelian.Devissage.SpanLayers

/-!
# Q-arrow lifts through a Serre quotient

Adapted from Quillen/Localization/Serre/AuxiliaryLift.lean at commit
c561118b7795eb9780be9ed391c3251d6a4d0afd.

An object of the auxiliary lift category over `V` is an ambient object `N`
with an isomorphism `L(N) ≅ V`; a morphism is an actual ambient arrow compatible
with these isomorphisms. The left calculus of fractions supplies common
successors and equalizers of parallel arrows, proving this category filtered.
The statements are first proved for any localization admitting that calculus,
then specialized to the canonical Serre quotient.

The module also proves fixed-target Q-arrow lifting, surjectivity and lattice
preservation of the quotient subobject map, and concrete join-semilattices of
lifted intervals with compatible quotient isomorphisms.

These are the ordinary lift categories appearing in the localization proof.
Their filteredness alone is not asserted to prove homotopical localization.
-/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ExactCategory.SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable (L : C ⥤ D) (V : D)
section SubobjectLifting

variable [Abelian C] [Abelian D]
  (P : ObjectProperty C) [P.IsSerreClass] [L.IsLocalization P.isoModSerre] [L.Additive]
include P

/-- Any quotient Q-span with a fixed localized target admits an ambient
admissible-span presentation. Both the source and apex identifications are
provided, and both legs commute with them. -/
theorem exists_span_lift {M : C} {V : D}
    (s : Span (abelianExactStructure D).deflation (abelianExactStructure D).inflation
      V (L.obj M)) :
    ∃ (X : C) (t : Span (abelianExactStructure C).deflation
      (abelianExactStructure C).inflation X M) (e : L.obj X ≅ V)
      (a : L.obj t.apex ≅ s.apex),
      L.map t.l ≫ e.hom = a.hom ≫ s.l ∧ L.map t.r = a.hom ≫ s.r := by
  have : Mono s.r := (abelianExactStructure D).mono_of_inflation s.wr
  have : Epi s.l := (abelianExactStructure D).epi_of_deflation s.wl
  obtain ⟨N, j, hj, a, ha⟩ := exists_mono_lift L P s.r
  obtain ⟨X, l, hl, e, he⟩ := exists_epi_lift L P (a.hom ≫ s.l)
  exact ⟨X, ⟨N, l, j, (abelianExactStructure_deflation_iff C l).2 hl,
    (abelianExactStructure_inflation_iff C j).2 hj⟩, e, a, he, ha⟩

set_option backward.isDefEq.respectTransparency false in
/-- Every Q-arrow ending in `L(M)` is the image of an ambient Q-arrow ending
in `M`, up to the explicitly supplied source isomorphism. The equality is in
the actual quotient-span Q-category, so representative choices are discharged. -/
theorem exists_qHom_lift {M : C} {V : D}
    (f : QConstruction.of (abelianExactStructure D).deflation
      (abelianExactStructure D).inflation V ⟶
      QConstruction.of (abelianExactStructure D).deflation
        (abelianExactStructure D).inflation (L.obj M)) :
    ∃ (X : C) (g : QConstruction.of (abelianExactStructure C).deflation
      (abelianExactStructure C).inflation X ⟶
      QConstruction.of (abelianExactStructure C).deflation (abelianExactStructure C).inflation M)
      (e : L.obj X ≅ V),
      (mapQ P L).map g = ((abelianExactStructure D).qIsoOfIso e).hom ≫ f := by
  induction f using Quotient.inductionOn with
  | _ s =>
    obtain ⟨X, t, e, a, hl, hr⟩ := exists_span_lift L P s
    refine ⟨X, QConstruction.mkHom _ _ t, e, ?_⟩
    let c := QConstruction.isoSpan (abelianExactStructure D).deflation
      (abelianExactStructure D).inflation e ((abelianExactStructure D).inflation_of_iso e)
    let sq : IsPullback (L.map t.l) a.hom e.hom s.l := IsPullback.of_vert_isIso ⟨hl⟩
    change QConstruction.mkHom _ _ ((CategoryTheory.ExactCategory.ExactFunctor.serreLocalization P
      L).toQCompatibleFunctor.mapSpan t) =
      QConstruction.mkHom _ _ (Span.comp c s)
    apply QConstruction.mkHom_eq_of_apexIso _ _ _ _ sq.isoPullback
    · change sq.isoPullback.hom ≫ pullback.fst e.hom s.l ≫ 𝟙 _ = L.map t.l
      simp
    · change sq.isoPullback.hom ≫ pullback.snd e.hom s.l ≫ s.r = L.map t.r
      simpa using hr.symm

/-- Localization carries the upper endpoint of a span's layer to the upper
endpoint of the localized span. -/
theorem subobjectMap_spanUpper {X M : C} (s : QConstruction.AbelianSpan X M) :
    subobjectMap L P M (Abelian.Devissage.spanUpper s) =
      Abelian.Devissage.spanUpper ((CategoryTheory.ExactCategory.ExactFunctor.serreLocalization P
        L).toQCompatibleFunctor.mapSpan s) := by
  let := ObjectProperty.SerreClassLocalization.preservesMonomorphisms L P
  exact subobjectMap_mk L P s.r

set_option backward.isDefEq.respectTransparency false in
/-- Exactness also carries the kernel/lower endpoint to the lower endpoint
of the localized span, with the actual preserved-kernel isomorphism. -/
theorem subobjectMap_spanLower {X M : C} (s : QConstruction.AbelianSpan X M) :
    subobjectMap L P M (Abelian.Devissage.spanLower s) =
      Abelian.Devissage.spanLower ((CategoryTheory.ExactCategory.ExactFunctor.serreLocalization P
        L).toQCompatibleFunctor.mapSpan s) := by
  let := ObjectProperty.SerreClassLocalization.preservesMonomorphisms L P
  let := ObjectProperty.SerreClassLocalization.preservesFiniteLimits L P
  rw [Abelian.Devissage.spanLower, subobjectMap_mk]
  change Subobject.mk (L.map (kernel.ι s.l ≫ s.r)) =
    Subobject.mk (kernel.ι (L.map s.l) ≫ L.map s.r)
  apply Subobject.mk_eq_mk_of_comm _ _ (PreservesKernel.iso L s.l)
  simp [PreservesKernel.iso_hom]

end SubobjectLifting
end CategoryTheory.ExactCategory.SerreLocalization
