/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.ExtensionBaseChange
public import Colib.CategoryTheory.ExactCategory.KernelComposition
public import Colib.CategoryTheory.ExactCategory.ExtensionProjectionCokernelComparison
public import Colib.CategoryTheory.ExactCategory.QSpanNaturality

/-!
Implementation provenance:
`Quillen/CategoryTheory/ExactCategory/ExtensionSpanLift.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Actual extension lifts of the original admissible Q-spans -/
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

/-- Transport only the source of the original span along a specified quotient iso. -/
def extensionLiftSpan {X : C} {x y : E.ExtensionTotal}
    (s : Span E.deflation E.inflation X (E.extensionProjectionObject y))
    (e : (E.extensionQuotientData x).obj ≅ X) :
    Span E.deflation E.inflation (E.extensionProjectionObject x)
      (E.extensionProjectionObject y) where
  apex := s.apex
  l := s.l ≫ e.inv
  r := s.r
  wl := E.deflation_comp _ _ s.wl (E.deflation_of_iso e.symm)
  wr := s.wr

/-- A lift with its actual source quotient iso and original Q-span equation.
No cartesian universal property is included in this intermediate construction. -/
structure ExtensionSpanLift {X : C} (y : E.ExtensionTotal)
    (s : Span E.deflation E.inflation X (E.extensionProjectionObject y)) where
  /-- The lifted source extension. -/
  source : E.ExtensionTotal
  /-- The actual total-extension arrow. -/
  hom : source ⟶ y
  /-- Its chosen quotient is canonically the prescribed source object. -/
  quotientIso : (E.extensionQuotientData source).obj ≅ X
  /-- Its projection is precisely the original span with this source identification. -/
  projection : E.extensionProjectionQMap hom =
    QConstruction.mkHom E.deflation E.inflation (E.extensionLiftSpan s quotientIso)

/-- Pull back along the inflation leg, then compose the quotient deflations.
This constructs a lift for every original Q-span representative. -/
def extensionSpanLift {X : C} (y : E.ExtensionTotal)
    (s : Span E.deflation E.inflation X (E.extensionProjectionObject y)) :
    E.ExtensionSpanLift y s := by
  let qy := E.extensionQuotientData y
  let : HasPullback qy.π s.r := E.deflation.hasPullback s.r
    (E.deflation_of_conflation qy.conflation)
  let p := pullback.snd qy.π s.r
  let b := pullback.fst qy.π s.r
  let i := (pullbackConflation s.apex s.r
    (S := ShortComplex.mk y.fiber.unop.hom.hom qy.π qy.zero)).f
  have hi := E.pullbackConflation_mem qy.conflation s.r
  let ps : E.ExtensionOver X := ⟨Over.mk (p ≫ s.l),
    E.deflation_comp _ _ (E.deflation_of_conflation hi) s.wl⟩
  let ks := E.extensionKernelData ps
  let kl := E.extensionKernelData (⟨Over.mk s.l, s.wl⟩ : E.ExtensionOver X)
  have zi : i ≫ p = 0 := (pullbackConflation s.apex s.r
    (S := ShortComplex.mk y.fiber.unop.hom.hom qy.π qy.zero)).zero
  have zic : i ≫ (p ≫ s.l) = 0 := by rw [← Category.assoc, zi, zero_comp]
  let a := (ks.isLimit E).lift (KernelFork.ofι i zic)
  have ha : a ≫ ks.ι = i := (ks.isLimit E).fac _ WalkingParallelPair.zero
  have haI : E.inflation a := E.inflation_kernelMap_comp hi kl.conflation ks.conflation a ha
  let x := E.extensionTotalOf ks.ι (E.inflation_of_conflation ks.conflation)
  have hb : E.inflation b := E.inflation_of_isPullback
    (IsPullback.of_hasPullback qy.π s.r).flip s.wr
      (E.deflation_of_conflation qy.conflation)
  let aw : y.fiber.unop.left ⟶ x.fiber.unop.left := ⟨a, haI⟩
  let bw : x.base ⟶ y.base := ⟨b, hb⟩
  let f : x ⟶ y := ⟨bw, (Over.homMk aw (by
    apply WideSubcategory.hom_ext
    change a ≫ ks.ι ≫ b = y.fiber.unop.hom.hom
    rw [← Category.assoc, ha]
    exact pullback.lift_fst _ _ _)).op⟩
  let qx := E.extensionQuotientData x
  let e := (qx.isColimit E).coconePointUniqueUpToIso (E.cokernel _ ks.conflation)
  have he : qx.π ≫ e.hom = p ≫ s.l :=
    (qx.isColimit E).comp_coconePointUniqueUpToIso_hom
      (E.cokernel _ ks.conflation) WalkingParallelPair.one
  refine ⟨x, f, e, ?_⟩
  have z : ((Subdivision.domainMap f).hom ≫ x.fiber.unop.hom.hom) ≫ p = 0 := by
    change (a ≫ ks.ι) ≫ p = 0
    rw [ha, zi]
  apply E.extensionProjectionQMap_eq_of_cokernel f (E.extensionLiftSpan s e) p z
  · exact CokernelCofork.isColimitOfIsColimitOfIff' (E.cokernel _ hi)
      (a ≫ ks.ι) (by intro W t; rw [ha])
  · change p ≫ (s.l ≫ e.inv) = qx.π
    rw [← Category.assoc, ← he]
    simp
  · exact pullback.condition.symm

/-- The lifted projection equation expressed using the original Q composition. -/
theorem ExtensionSpanLift.projection_comp {X : C} {y : E.ExtensionTotal}
    {s : Span E.deflation E.inflation X (E.extensionProjectionObject y)}
    (l : E.ExtensionSpanLift y s) :
    E.extensionProjectionQMap l.hom =
      (E.qIsoOfIso l.quotientIso).hom ≫ QConstruction.mkHom E.deflation E.inflation s := by
  rw [l.projection]
  have h := E.qSpan_iso_naturality (E.extensionLiftSpan s l.quotientIso) s
    l.quotientIso (Iso.refl _) (Iso.refl _)
    (by simp [extensionLiftSpan]) (by simp [extensionLiftSpan])
  change QConstruction.mkHom _ _ (E.extensionLiftSpan s l.quotientIso) ≫ 𝟙 _ = _ at h
  simpa only [Category.comp_id] using h

/-- Every arrow in the original Q quotient admits an actual extension lift
up to the specified canonical source isomorphism. The cartesian uniqueness
and fiber-to-comma comparison remain separate obligations. -/
theorem exists_extensionLift {X : C} (y : E.ExtensionTotal)
    (g : QConstruction.of E.deflation E.inflation X ⟶ E.extensionProjectionQObj y) :
    ∃ (x : E.ExtensionTotal) (e : (E.extensionQuotientData x).obj ≅ X) (f : x ⟶ y),
      E.extensionProjectionQMap f = (E.qIsoOfIso e).hom ≫ g := by
  obtain ⟨s, rfl⟩ := Quotient.exists_rep g
  let l := E.extensionSpanLift y s
  exact ⟨l.source, l.quotientIso, l.hom, l.projection_comp E⟩

end CategoryTheory.ExactCategory.ExactStructure
