/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.ExtensionSpanLift
public import Colib.CategoryTheory.ExactCategory.ExtensionTotalIsomorphism

/-!
Implementation provenance:
`Quillen/CategoryTheory/ExactCategory/ExtensionCartesianComparison.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Comparing actual extension arrows over the same original Q-arrow -/
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

/-- Two extension arrows over the same Q-arrow, after the specified source
isomorphism, admit an actual source isomorphism over that identification. -/
theorem exists_extensionComparisonIso {x y z : E.ExtensionTotal}
    (f : x ⟶ z) (g : y ⟶ z)
    (e : (E.extensionQuotientData x).obj ≅ (E.extensionQuotientData y).obj)
    (w : E.extensionProjectionQMap f = (E.qIsoOfIso e).hom ≫ E.extensionProjectionQMap g) :
    ∃ a : x ≅ y, a.hom ≫ g = f ∧
      E.extensionProjectionQMap a.hom = (E.qIsoOfIso e).hom := by
  let s := E.extensionProjectionSpan f
  let t := E.extensionProjectionSpan g
  let t' := E.extensionLiftSpan (x := x) t e
  have ht : QConstruction.mkHom _ _ t' = (E.qIsoOfIso e).hom ≫ QConstruction.mkHom _ _ t := by
    have h := E.qSpan_iso_naturality t' t e (Iso.refl _) (Iso.refl _)
      (by simp [t', extensionLiftSpan]) (by simp [t', extensionLiftSpan])
    change QConstruction.mkHom _ _ t' ≫ 𝟙 _ = _ at h
    simpa only [Category.comp_id] using h
  have hs : QConstruction.mkHom _ _ s = QConstruction.mkHom _ _ t' := w.trans ht.symm
  obtain ⟨a, al, ar⟩ := (QConstruction.mkHom_eq_iff_apexIso _ _ _ _).1 hs
  change a.hom ≫ (t.l ≫ e.inv) = s.l at al
  change a.hom ≫ t.r = s.r at ar
  have al' : a.hom ≫ t.l = s.l ≫ e.hom := by
    rw [← al]
    simp
  let qf := E.extensionProjectionCokernel f
  let qg := E.extensionProjectionCokernel g
  let sf := E.extensionProjection_right_isPullback f
  let sg := E.extensionProjection_right_isPullback g
  have sg' : IsPullback g.base.hom (qg.π ≫ a.inv)
      (E.extensionQuotientData z).π s.r := by
    apply sg.of_iso (Iso.refl _) (Iso.refl _) a.symm (Iso.refl _)
    · simp
    · simp
      rfl
    · simp
    · change t.r ≫ 𝟙 _ = a.inv ≫ s.r
      rw [← ar]
      simp
  let b := sf.isoIsPullback _ _ sg'
  have hb : b.hom ≫ g.base.hom = f.base.hom := sf.isoIsPullback_hom_fst _ _ sg'
  have hbq : b.hom ≫ qg.π = qf.π ≫ a.hom := by
    apply (cancel_mono a.inv).1
    have h := sf.isoIsPullback_hom_snd _ _ sg'
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h
  have wb : (E.extensionQuotientData x).π ≫ e.hom =
      b.hom ≫ (E.extensionQuotientData y).π := by
    rw [← qf.left, ← qg.left, ← Category.assoc, hbq]
    change (qf.π ≫ s.l) ≫ e.hom = (qf.π ≫ a.hom) ≫ t.l
    simp only [Category.assoc, al']
  let c := E.extensionIsoOfQuotientSquare b e wb
  refine ⟨c, ?_, E.extensionIsoOfQuotientSquare_projection b e wb⟩
  apply E.extensionTotalMiddle.map_injective
  exact hb

end CategoryTheory.ExactCategory.ExactStructure
