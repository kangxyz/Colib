/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.Extensions.Basic
public import Colib.CategoryTheory.ExactCategory.ExtensionTotalIsomorphism
public import Colib.CategoryTheory.ExactCategory.ExtensionProjectionConservative
public import Colib.CategoryTheory.FiberedCategory.IsoFiber.Basic

/-!
Implementation provenance:
`Quillen/CategoryTheory/ExactCategory/ExtensionDeflationEntry.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Actual deflations enter the original total extension category -/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- The actual kernel of a deflation, as an original admissible inflation. -/
def extensionOfDeflation {X : C} (p : E.ExtensionOver X) : E.ExtensionTotal :=
  E.extensionTotalOf (E.extensionKernelData p).ι
    (E.inflation_of_conflation (E.extensionKernelData p).conflation)

/-- The original deflation is a quotient presentation of its chosen kernel. -/
def extensionOfDeflationQuotient {X : C} (p : E.ExtensionOver X) :
    E.ExtensionQuotientData (E.extensionOfDeflation p) where
  obj := X
  π := p.obj.hom
  zero := (E.extensionKernelData p).zero
  conflation := (E.extensionKernelData p).conflation

/-- Chosen quotients are identified with the unchanged prescribed quotient. -/
def extensionOfDeflationQuotientIso {X : C} (p : E.ExtensionOver X) :
    (E.extensionQuotientData (E.extensionOfDeflation p)).obj ≅ X :=
  (E.extensionQuotientData (E.extensionOfDeflation p)).iso E
    (E.extensionOfDeflationQuotient p)

@[reassoc (attr := simp)]
lemma extensionOfDeflationQuotientIso_π {X : C} (p : E.ExtensionOver X) :
    (E.extensionQuotientData (E.extensionOfDeflation p)).π ≫
      (E.extensionOfDeflationQuotientIso p).hom = p.obj.hom :=
  ExtensionQuotientData.π_iso_hom E _ _

/-- An isomorphism over the original quotient determines a genuine isomorphism
of the chosen-kernel total extensions. -/
def extensionOfDeflationMapIso {X : C} {p q : E.ExtensionOver X} (g : p ≅ q) :
    E.extensionOfDeflation p ≅ E.extensionOfDeflation q :=
  E.extensionIsoOfQuotientSquare ((E.extensionMiddle X).mapIso g)
    (E.extensionOfDeflationQuotientIso p ≪≫ (E.extensionOfDeflationQuotientIso q).symm)
    (by
      apply (cancel_mono (E.extensionOfDeflationQuotientIso q).hom).1
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
        Category.comp_id, extensionOfDeflationQuotientIso_π]
      change p.obj.hom = g.hom.hom.left ≫ q.obj.hom
      exact (Over.w g.hom.hom).symm)

@[simp]
lemma extensionOfDeflationMapIso_base {X : C} {p q : E.ExtensionOver X} (g : p ≅ q) :
    (E.extensionOfDeflationMapIso g).hom.base.hom = g.hom.hom.left := rfl

/-- The groupoid of deflations over a fixed quotient enters the original total category. -/
def extensionDeflationEntry (X : C) : E.ExtensionFiber X ⥤ E.ExtensionTotal where
  obj p := E.extensionOfDeflation p.of
  map f := (E.extensionOfDeflationMapIso f.iso).hom
  map_id p := by
    apply E.extensionTotalMiddle.map_injective
    rfl
  map_comp f g := by
    apply E.extensionTotalMiddle.map_injective
    rfl

@[simp]
lemma extensionDeflationEntry_map_base {X : C} {p q : E.ExtensionFiber X} (f : p ⟶ q) :
    ((E.extensionDeflationEntry X).map f).base.hom = f.iso.hom.hom.left := rfl

/-- The chosen-kernel isomorphism projects to its unchanged original quotient square. -/
lemma extensionOfDeflationMapIso_projection {X : C} {p q : E.ExtensionOver X} (g : p ≅ q) :
    E.extensionProjectionQMap (E.extensionOfDeflationMapIso g).hom =
      (E.qIsoOfIso (E.extensionOfDeflationQuotientIso p ≪≫
        (E.extensionOfDeflationQuotientIso q).symm)).hom := by
  unfold extensionOfDeflationMapIso
  exact E.extensionIsoOfQuotientSquare_projection _ _ _

/-- The prescribed original quotient is naturally isomorphic to the chosen
quotient of the actual total extension. -/
def extensionDeflationProjectionIso (X : C) :
    E.extensionDeflationEntry X ⋙ E.extensionProjection ≅
      (Functor.const (E.ExtensionFiber X)).obj (QConstruction.of E.deflation E.inflation X) :=
  NatIso.ofComponents (fun p ↦ E.qIsoOfIso (E.extensionOfDeflationQuotientIso p.of)) (by
    intro p q f
    change E.extensionProjectionQMap (E.extensionOfDeflationMapIso f.iso).hom ≫
      (E.qIsoOfIso (E.extensionOfDeflationQuotientIso q.of)).hom =
      (E.qIsoOfIso (E.extensionOfDeflationQuotientIso p.of)).hom ≫ 𝟙 _
    rw [extensionOfDeflationMapIso_projection, Category.comp_id]
    rw [← Iso.trans_hom, ← E.qIsoOfIso_trans]
    congr 2
    exact Iso.ext (by simp))

/-- Deflations enter the actual isomorphism fiber over the original Q object. -/
def extensionDeflationIsoFiber (X : C) :
    E.ExtensionFiber X ⥤
      IsoFiber E.extensionProjection (QConstruction.of E.deflation E.inflation X) :=
  IsoFiber.lift E.extensionProjection _ (E.extensionDeflationEntry X)
    (E.extensionDeflationProjectionIso X).symm

instance extensionDeflationIsoFiber_faithful (X : C) :
    (E.extensionDeflationIsoFiber X).Faithful where
  map_injective {_ _} f g h := by
    apply Core.hom_ext
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact congrArg (fun k ↦ k.hom.right.base.hom) h

/-- Equality with an original Q isomorphism recovers its actual quotient square. -/
lemma extensionProjection_square_of_eq_qIso {x y : E.ExtensionTotal} (f : x ⟶ y)
    (e : (E.extensionQuotientData x).obj ≅ (E.extensionQuotientData y).obj)
    (h : E.extensionProjectionQMap f = (E.qIsoOfIso e).hom) :
    (E.extensionQuotientData x).π ≫ e.hom =
      f.base.hom ≫ (E.extensionQuotientData y).π := by
  obtain ⟨a, hl, hr⟩ := (QConstruction.mkHom_eq_iff_apexIso _ _ _ _).1 h
  have hl' : a.hom = (E.extensionProjectionSpan f).l := by
    simpa only [QConstruction.isoSpan, Category.comp_id] using hl
  have hr' : (E.extensionProjectionSpan f).l ≫ e.hom =
      (E.extensionProjectionSpan f).r := by
    simpa only [QConstruction.isoSpan, hl'] using hr
  rw [← (E.extensionProjectionCokernel f).left, Category.assoc, hr']
  exact (E.extensionProjectionCokernel f).right

/-- Every arrow in the original isomorphism fiber is an isomorphism over the
prescribed quotient; the quotient equation is recovered from the Q span. -/
instance extensionDeflationIsoFiber_full (X : C) :
    (E.extensionDeflationIsoFiber X).Full where
  map_surjective {p q} f := by
    let k := f.hom.right
    let e := E.extensionOfDeflationQuotientIso p.of ≪≫
      (E.extensionOfDeflationQuotientIso q.of).symm
    have hk : E.extensionProjectionQMap k = (E.qIsoOfIso e).hom := by
      have hw := f.hom.w
      change (E.qIsoOfIso (E.extensionOfDeflationQuotientIso p.of)).inv ≫
        E.extensionProjectionQMap k =
        (E.qIsoOfIso (E.extensionOfDeflationQuotientIso q.of)).inv at hw
      apply (cancel_epi
        (E.qIsoOfIso (E.extensionOfDeflationQuotientIso p.of)).inv).1
      rw [hw]
      dsimp only [e]
      rw [E.qIsoOfIso_trans, Iso.trans_hom]
      change _ = _ ≫ ((E.qIsoOfIso _).hom ≫ (E.qIsoOfIso _).inv)
      simp
    let : IsIso (E.extensionProjectionQMap k) := hk ▸ inferInstance
    let : IsIso k.base.hom := E.extensionProjection_isIso_base k
    have w := E.extensionProjection_square_of_eq_qIso k e hk
    have w' : k.base.hom ≫ q.of.obj.hom = p.of.obj.hom := by
      change (E.extensionQuotientData (E.extensionOfDeflation p.of)).π ≫ e.hom =
        k.base.hom ≫ (E.extensionQuotientData (E.extensionOfDeflation q.of)).π at w
      have w'' := congrArg (fun z ↦ z ≫ (E.extensionOfDeflationQuotientIso q.of).hom) w
      simpa only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc,
        Iso.inv_hom_id, Category.comp_id, extensionOfDeflationQuotientIso_π] using w''.symm
    let g : p.of ≅ q.of := (E.extensionProperty X).isoMk
      (Over.isoMk (asIso k.base.hom) w')
    refine ⟨⟨g⟩, ?_⟩
    apply ObjectProperty.hom_ext
    apply StructuredArrow.hom_ext
    apply E.extensionTotalMiddle.map_injective
    rfl

/-- Every extension equipped with an original quotient isomorphism is represented
by its actual deflation to that prescribed quotient. -/
instance extensionDeflationIsoFiber_essSurj (X : C) :
    (E.extensionDeflationIsoFiber X).EssSurj where
  mem_essImage U := by
    let x := U.obj.right
    obtain ⟨e, he⟩ := E.qIsoOfIso_bijective.surjective (asIso U.obj.hom)
    let p : E.ExtensionOver X := ⟨Over.mk ((E.extensionQuotientData x).π ≫ e.inv),
      E.deflation_comp _ _ (E.deflation_of_conflation (E.extensionQuotientData x).conflation)
        (E.deflation_of_iso e.symm)⟩
    let a := E.extensionOfDeflationQuotientIso p ≪≫ e
    have w : (E.extensionQuotientData (E.extensionOfDeflation p)).π ≫ a.hom =
        (Iso.refl x.base.obj).hom ≫ (E.extensionQuotientData x).π := by
      dsimp only [a, Iso.trans_hom, Iso.refl_hom]
      rw [← Category.assoc, extensionOfDeflationQuotientIso_π]
      change ((E.extensionQuotientData x).π ≫ e.inv) ≫ e.hom = _
      simp
    let t : E.extensionOfDeflation p ≅ x := E.extensionIsoOfQuotientSquare
      (Iso.refl x.base.obj) a w
    refine ⟨⟨p⟩, ⟨(isoFiberProperty E.extensionProjection _).isoMk
      (StructuredArrow.isoMk t ?_)⟩⟩
    change (E.qIsoOfIso (E.extensionOfDeflationQuotientIso p)).inv ≫
      E.extensionProjectionQMap t.hom = U.obj.hom
    rw [E.extensionIsoOfQuotientSquare_projection]
    dsimp only [a]
    rw [E.qIsoOfIso_trans, Iso.trans_hom, Iso.inv_hom_id_assoc, he]
    rfl

instance extensionDeflationIsoFiber_isEquivalence (X : C) :
    (E.extensionDeflationIsoFiber X).IsEquivalence where

/-- The actual fixed-deflation groupoid is equivalent to the original total
projection's isomorphism fiber, preserving the specified quotient isomorphism. -/
def extensionDeflationIsoFiberEquivalence (X : C) :
    E.ExtensionFiber X ≌
      IsoFiber E.extensionProjection (QConstruction.of E.deflation E.inflation X) :=
  (E.extensionDeflationIsoFiber X).asEquivalence

end CategoryTheory.ExactCategory.ExactStructure
