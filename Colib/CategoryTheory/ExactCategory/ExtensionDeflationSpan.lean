/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.ExtensionDeflationEntry
public import Colib.CategoryTheory.ExactCategory.ExtensionSpanLift

/-!
Implementation provenance:
`Quillen/CategoryTheory/ExactCategory/ExtensionDeflationSpan.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Original Q-span lifts on the unchanged fixed-deflation model -/
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

/-- Pullbacks are supplied by the original deflation axiom. -/
local instance deflationSpanHasPullback {X Y : C}
    (s : Span E.deflation E.inflation X Y) (p : E.ExtensionFiber Y) :
    HasPullback p.of.obj.hom s.r := E.deflation.hasPullback s.r p.of.property

/-- The actual pullback projection is a total-extension arrow from the original
fixed-deflation span transport, retaining both chosen kernel objects. -/
def extensionDeflationSpanHom {X Y : C} (s : Span E.deflation E.inflation X Y)
    (p : E.ExtensionFiber Y) :
    E.extensionOfDeflation ((E.extensionSpanTransport s).obj p).of ⟶
      E.extensionOfDeflation p.of := by
  let ky := E.extensionKernelData p.of
  let : HasPullback p.of.obj.hom s.r := E.deflation.hasPullback s.r p.of.property
  let q := pullback.snd p.of.obj.hom s.r
  let b := pullback.fst p.of.obj.hom s.r
  let i := (pullbackConflation s.apex s.r
    (S := ShortComplex.mk ky.ι p.of.obj.hom ky.zero)).f
  have hi := E.pullbackConflation_mem ky.conflation s.r
  let ps := ((E.extensionSpanTransport s).obj p).of
  let ks := E.extensionKernelData ps
  let kl := E.extensionKernelData (⟨Over.mk s.l, s.wl⟩ : E.ExtensionOver X)
  have zi : i ≫ q = 0 := (pullbackConflation s.apex s.r
    (S := ShortComplex.mk ky.ι p.of.obj.hom ky.zero)).zero
  have zic : i ≫ ps.obj.hom = 0 := by
    change i ≫ (q ≫ s.l) = 0
    rw [← Category.assoc, zi, zero_comp]
  let a := (ks.isLimit E).lift (KernelFork.ofι i zic)
  have ha : a ≫ ks.ι = i := (ks.isLimit E).fac _ WalkingParallelPair.zero
  have haI : E.inflation a := E.inflation_kernelMap_comp hi kl.conflation ks.conflation a ha
  have hb : E.inflation b := E.inflation_of_isPullback
    (IsPullback.of_hasPullback p.of.obj.hom s.r).flip s.wr p.of.property
  let aw : (E.extensionOfDeflation p.of).fiber.unop.left ⟶
      (E.extensionOfDeflation ps).fiber.unop.left := ⟨a, haI⟩
  let bw : (E.extensionOfDeflation ps).base ⟶ (E.extensionOfDeflation p.of).base := ⟨b, hb⟩
  refine ⟨bw, (Over.homMk aw ?_).op⟩
  apply WideSubcategory.hom_ext
  change a ≫ ks.ι ≫ b = ky.ι
  rw [← Category.assoc, ha]
  exact pullback.lift_fst _ _ _

/-- The lift retains exactly the original pullback's middle-object projection. -/
@[simp]
lemma extensionDeflationSpanHom_base {X Y : C} (s : Span E.deflation E.inflation X Y)
    (p : E.ExtensionFiber Y) :
    (E.extensionDeflationSpanHom s p).base.hom = pullback.fst p.of.obj.hom s.r := rfl

/-- Transport the endpoints of the original span only by the canonical chosen
quotient isomorphisms; its original apex is retained. -/
def extensionDeflationProjectionSpan {X Y : C} (s : Span E.deflation E.inflation X Y)
    (p : E.ExtensionFiber Y) :
    Span E.deflation E.inflation
      (E.extensionProjectionObject (E.extensionOfDeflation ((E.extensionSpanTransport s).obj p).of))
      (E.extensionProjectionObject (E.extensionOfDeflation p.of)) where
  apex := s.apex
  l := s.l ≫ (E.extensionOfDeflationQuotientIso ((E.extensionSpanTransport s).obj p).of).inv
  r := s.r ≫ (E.extensionOfDeflationQuotientIso p.of).inv
  wl := E.deflation_comp _ _ s.wl (E.deflation_of_iso
    (E.extensionOfDeflationQuotientIso ((E.extensionSpanTransport s).obj p).of).symm)
  wr := E.inflation_comp _ _ s.wr
    (E.inflation_of_iso (E.extensionOfDeflationQuotientIso p.of).symm)

/-- The actual total arrow projects to the original span with exactly the two
canonical endpoint quotient identifications. -/
lemma extensionDeflationSpanHom_projection {X Y : C}
    (s : Span E.deflation E.inflation X Y) (p : E.ExtensionFiber Y) :
    E.extensionProjectionQMap (E.extensionDeflationSpanHom s p) =
      QConstruction.mkHom E.deflation E.inflation (E.extensionDeflationProjectionSpan s p) := by
  let ky := E.extensionKernelData p.of
  let ps := ((E.extensionSpanTransport s).obj p).of
  let ks := E.extensionKernelData ps
  let q := pullback.snd p.of.obj.hom s.r
  let i := (pullbackConflation s.apex s.r
    (S := ShortComplex.mk ky.ι p.of.obj.hom ky.zero)).f
  let f := E.extensionDeflationSpanHom s p
  have hi := E.pullbackConflation_mem ky.conflation s.r
  have zi : i ≫ q = 0 := (pullbackConflation s.apex s.r
    (S := ShortComplex.mk ky.ι p.of.obj.hom ky.zero)).zero
  have zic : i ≫ ps.obj.hom = 0 := by
    change i ≫ (q ≫ s.l) = 0
    rw [← Category.assoc, zi, zero_comp]
  have ha : (Subdivision.domainMap f).hom ≫ ks.ι = i :=
    (ks.isLimit E).fac (KernelFork.ofι i zic) WalkingParallelPair.zero
  have z : ((Subdivision.domainMap f).hom ≫ ks.ι) ≫ q = 0 := by rw [ha, zi]
  apply E.extensionProjectionQMap_eq_of_cokernel f
    (E.extensionDeflationProjectionSpan s p) q z
  · exact CokernelCofork.isColimitOfIsColimitOfIff' (E.cokernel _ hi)
      ((Subdivision.domainMap f).hom ≫ ks.ι) (by intro W t; rw [ha])
  · change q ≫ (s.l ≫ (E.extensionOfDeflationQuotientIso ps).inv) =
      (E.extensionQuotientData (E.extensionOfDeflation ps)).π
    apply (cancel_mono (E.extensionOfDeflationQuotientIso ps).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      extensionOfDeflationQuotientIso_π]
    rfl
  · change q ≫ (s.r ≫ (E.extensionOfDeflationQuotientIso p.of).inv) =
      (pullback.fst p.of.obj.hom s.r) ≫
        (E.extensionQuotientData (E.extensionOfDeflation p.of)).π
    apply (cancel_mono (E.extensionOfDeflationQuotientIso p.of).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      extensionOfDeflationQuotientIso_π]
    exact pullback.condition.symm

/-- The original Q-span and canonical fixed-fiber entry form the precise
commuting square needed for the structured-comma transition. -/
lemma extensionDeflationSpanHom_over {X Y : C}
    (s : Span E.deflation E.inflation X Y) (p : E.ExtensionFiber Y) :
    (E.qIsoOfIso (E.extensionOfDeflationQuotientIso
      ((E.extensionSpanTransport s).obj p).of)).inv ≫
        E.extensionProjectionQMap (E.extensionDeflationSpanHom s p) =
      QConstruction.mkHom E.deflation E.inflation s ≫
        (E.qIsoOfIso (E.extensionOfDeflationQuotientIso p.of)).inv := by
  have h := E.qSpan_iso_naturality (E.extensionDeflationProjectionSpan s p) s
    (E.extensionOfDeflationQuotientIso ((E.extensionSpanTransport s).obj p).of)
    (E.extensionOfDeflationQuotientIso p.of) (Iso.refl _)
    (by simp [extensionDeflationProjectionSpan])
    (by simp [extensionDeflationProjectionSpan])
  rw [extensionDeflationSpanHom_projection]
  apply (cancel_mono (E.qIsoOfIso (E.extensionOfDeflationQuotientIso p.of)).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h]
  simp

/-- The actual pullback projections are natural in the unchanged fixed-deflation
isomorphisms; naturality is detected on the original middle objects. -/
def extensionDeflationSpanNatTrans {X Y : C} (s : Span E.deflation E.inflation X Y) :
    E.extensionSpanTransport s ⋙ E.extensionDeflationEntry X ⟶ E.extensionDeflationEntry Y where
  app p := E.extensionDeflationSpanHom s p
  naturality {p q} f := by
    apply E.extensionTotalMiddle.map_injective
    change (pullback.lift (pullback.fst p.of.obj.hom s.r ≫ f.iso.hom.hom.left)
      (pullback.snd p.of.obj.hom s.r) _) ≫ pullback.fst q.of.obj.hom s.r =
      pullback.fst p.of.obj.hom s.r ≫ f.iso.hom.hom.left
    exact pullback.lift_fst _ _ _

/-- The original Q-span transport and actual fiber entries commute up to an
explicit natural arrow in the original structured-comma category. -/
def extensionDeflationSpanComma {X Y : C} (s : Span E.deflation E.inflation X Y) :
    E.extensionSpanTransport s ⋙ E.extensionDeflationIsoFiber X ⋙
      IsoFiber.toStructured E.extensionProjection (QConstruction.of E.deflation E.inflation X) ⟶
    E.extensionDeflationIsoFiber Y ⋙
      IsoFiber.toStructured E.extensionProjection (QConstruction.of E.deflation E.inflation Y) ⋙
      StructuredArrow.map (T := E.extensionProjection)
        (QConstruction.mkHom E.deflation E.inflation s) where
  app p := StructuredArrow.homMk (E.extensionDeflationSpanHom s p)
    (E.extensionDeflationSpanHom_over s p)
  naturality {p q} f := by
    apply StructuredArrow.hom_ext
    exact (E.extensionDeflationSpanNatTrans s).naturality f

end CategoryTheory.ExactCategory.ExactStructure
