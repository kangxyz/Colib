/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.ExtensionTotal
public import Colib.CategoryTheory.ExactCategory.ExtensionQuotientSpan

/-!
Implementation provenance:
`Quillen/CategoryTheory/ExactCategory/ExtensionProjection.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# The quotient-span assignment for the extension projection

This constructs the actual original Q-span for each total extension arrow.
Identity and composition in the Q quotient remain separate obligations; no
functor is asserted until those laws are proved.
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

/-- The quotient assigned to a total extension object. -/
def extensionProjectionObject (x : E.ExtensionTotal) : C := (E.extensionQuotientData x).obj

/-- The original admissible span assigned to an actual total extension morphism. -/
def extensionProjectionSpan {x y : E.ExtensionTotal} (f : x ⟶ y) :
    Span E.deflation E.inflation (E.extensionProjectionObject x)
      (E.extensionProjectionObject y) := by
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
      (by simpa only [Category.assoc] using zY)) := by
    simpa only [w] using qY.conflation
  exact E.quotientSpanOfInflations h i k qH.π qX.π qY.π
    qH.zero qX.zero zY qH.conflation qX.conflation cY f.base.property

/-- The quotient assignment lands in the original Q construction. -/
def extensionProjectionQObj (x : E.ExtensionTotal) : QConstruction E.deflation E.inflation :=
  QConstruction.of E.deflation E.inflation (E.extensionProjectionObject x)

/-- The actual Q morphism represented by the proved admissible quotient span.
Functoriality is not yet asserted. -/
def extensionProjectionQMap {x y : E.ExtensionTotal} (f : x ⟶ y) :
    E.extensionProjectionQObj x ⟶ E.extensionProjectionQObj y :=
  QConstruction.mkHom E.deflation E.inflation (E.extensionProjectionSpan f)

end CategoryTheory.ExactCategory.ExactStructure
