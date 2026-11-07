/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.ExtensionProjection
public import Colib.CategoryTheory.ExactCategory.ExtensionQuotientSpanCharacterization
public import Colib.CategoryTheory.Limits.Shapes.CokernelSquare
public import Colib.CategoryTheory.ExactCategory.Bicartesian

/-!
Implementation provenance:
`Quillen/CategoryTheory/ExactCategory/ExtensionProjectionGeometry.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # The actual quotient maps and bicartesian squares of the extension projection -/
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

/-- Universal-property data for the already constructed quotient span. -/
structure ExtensionProjectionCokernel {x y : E.ExtensionTotal} (f : x ⟶ y) where
  /-- Quotient from the original middle object to the span apex. -/
  π : x.base.obj ⟶ (E.extensionProjectionSpan f).apex
  /-- The smaller subobject is annihilated. -/
  zero : ((Subdivision.domainMap f).hom ≫ x.fiber.unop.hom.hom) ≫ π = 0
  /-- The span apex is the actual cokernel of the smaller subobject. -/
  isColimit : IsColimit (CokernelCofork.ofπ π zero)
  /-- The left leg recovers the source quotient. -/
  left : π ≫ (E.extensionProjectionSpan f).l = (E.extensionQuotientData x).π
  /-- The right leg recovers the target quotient after the middle-object map. -/
  right : π ≫ (E.extensionProjectionSpan f).r = f.base.hom ≫ (E.extensionQuotientData y).π

/-- Recover universal-property data from the proved span construction. -/
def extensionProjectionCokernel {x y : E.ExtensionTotal} (f : x ⟶ y) :
    E.ExtensionProjectionCokernel f := by
  let h := (Subdivision.domainMap f).hom
  let i := x.fiber.unop.hom.hom
  let k := f.base.hom
  have w : (h ≫ i) ≫ k = y.fiber.unop.hom.hom := by
    have hw := congrArg (fun a => a.hom) (Subdivision.factorization f)
    simpa only [WideSubcategory.comp_def, Category.assoc] using hw
  let qH := E.extensionQuotientData
    (E.extensionTotalOf h (Subdivision.domainMap f).property)
  let qX := E.extensionQuotientData x
  let qY := E.extensionQuotientData y
  have zY : (h ≫ i) ≫ k ≫ qY.π = 0 := by rw [← Category.assoc, w]; exact qY.zero
  have cY : E.conflation (ShortComplex.mk ((h ≫ i) ≫ k) qY.π
      (by simpa only [Category.assoc] using zY)) := by simpa only [w] using qY.conflation
  exact
    { π := QuotientSpan.projection E h i k qH.π qX.π qY.π
        qH.zero qX.zero zY qH.conflation qX.conflation cY f.base.property
      zero := QuotientSpan.projection_zero E h i k qH.π qX.π qY.π
        qH.zero qX.zero zY qH.conflation qX.conflation cY f.base.property
      isColimit := QuotientSpan.projectionIsCokernel E h i k qH.π qX.π qY.π
        qH.zero qX.zero zY qH.conflation qX.conflation cY f.base.property
      left := QuotientSpan.projection_left E h i k qH.π qX.π qY.π
        qH.zero qX.zero zY qH.conflation qX.conflation cY f.base.property
      right := QuotientSpan.projection_right E h i k qH.π qX.π qY.π
        qH.zero qX.zero zY qH.conflation qX.conflation cY f.base.property }

/-- The right-hand quotient square is a genuine pushout. -/
theorem extensionProjection_right_isPushout {x y : E.ExtensionTotal} (f : x ⟶ y) :
    IsPushout f.base.hom (E.extensionProjectionCokernel f).π
      (E.extensionQuotientData y).π (E.extensionProjectionSpan f).r := by
  let q := E.extensionProjectionCokernel f
  let j := (Subdivision.domainMap f).hom ≫ x.fiber.unop.hom.hom
  have w : j ≫ f.base.hom = y.fiber.unop.hom.hom := by
    have hw := congrArg (fun a => a.hom) (Subdivision.factorization f)
    simpa only [j, WideSubcategory.comp_def, Category.assoc] using hw
  have z : (j ≫ f.base.hom) ≫ (E.extensionQuotientData y).π = 0 := by
    rw [w]
    exact (E.extensionQuotientData y).zero
  have hy : IsColimit (CokernelCofork.ofπ (E.extensionQuotientData y).π z) :=
    CokernelCofork.isColimitOfIsColimitOfIff' ((E.extensionQuotientData y).isColimit E)
      (j ≫ f.base.hom) (by intro W a; rw [w])
  exact isPushout_of_cokernels j f.base.hom q.π (E.extensionQuotientData y).π
    (E.extensionProjectionSpan f).r q.zero z q.isColimit hy q.right.symm

/-- The same original quotient square is a pullback, not merely abstractly equivalent to one. -/
theorem extensionProjection_right_isPullback {x y : E.ExtensionTotal} (f : x ⟶ y) :
    IsPullback f.base.hom (E.extensionProjectionCokernel f).π
      (E.extensionQuotientData y).π (E.extensionProjectionSpan f).r :=
  E.isPullback_of_inflation_isPushout f.base.property (E.extensionProjection_right_isPushout f)

end CategoryTheory.ExactCategory.ExactStructure
