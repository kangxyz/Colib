/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.ExtensionProjectionGeometry

/-!
Implementation provenance:
`Quillen/CategoryTheory/ExactCategory/ExtensionProjectionCokernelComparison.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Recognition of original projection spans by their cokernel presentations -/
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

/-- A specified cokernel of the smaller subobject identifies the actual
projection arrow with a specified admissible span in the original Q quotient. -/
theorem extensionProjectionQMap_eq_of_cokernel {x y : E.ExtensionTotal} (f : x ⟶ y)
    (s : Span E.deflation E.inflation (E.extensionProjectionObject x)
      (E.extensionProjectionObject y))
    (p : x.base.obj ⟶ s.apex)
    (z : ((Subdivision.domainMap f).hom ≫ x.fiber.unop.hom.hom) ≫ p = 0)
    (hp : IsColimit (CokernelCofork.ofπ p z))
    (hl : p ≫ s.l = (E.extensionQuotientData x).π)
    (hr : p ≫ s.r = f.base.hom ≫ (E.extensionQuotientData y).π) :
    E.extensionProjectionQMap f = QConstruction.mkHom E.deflation E.inflation s := by
  let q := E.extensionProjectionCokernel f
  let a := q.isColimit.coconePointUniqueUpToIso hp
  have ha : q.π ≫ a.hom = p :=
    q.isColimit.comp_coconePointUniqueUpToIso_hom hp WalkingParallelPair.one
  let : Epi q.π := Cofork.IsColimit.epi q.isColimit
  apply QConstruction.mkHom_eq_of_apexIso E.deflation E.inflation _ _ a
  · apply (cancel_epi q.π).1
    rw [← Category.assoc, ha, hl, q.left]
  · apply (cancel_epi q.π).1
    rw [← Category.assoc, ha, hr, q.right]

end CategoryTheory.ExactCategory.ExactStructure
