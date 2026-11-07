/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.ExtensionProjectionGeometry
public import Colib.CategoryTheory.ExactCategory.QIsomorphisms

/-!
Implementation provenance:
`Quillen/CategoryTheory/ExactCategory/ExtensionProjectionIsomorphism.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Recognizing extension projection arrows induced by quotient isomorphisms -/
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

/-- When the reversed kernel map is epi, a compatible quotient isomorphism
represents exactly the original extension projection arrow. -/
theorem extensionProjectionQMap_eq_qIsoOfIso {x y : E.ExtensionTotal} (f : x ⟶ y)
    [Epi (Subdivision.domainMap f).hom]
    (e : (E.extensionQuotientData x).obj ≅ (E.extensionQuotientData y).obj)
    (he : (E.extensionQuotientData x).π ≫ e.hom = f.base.hom ≫
      (E.extensionQuotientData y).π) : E.extensionProjectionQMap f = (E.qIsoOfIso e).hom := by
  let q := E.extensionProjectionCokernel f
  let hc := isCokernelEpiComp ((E.extensionQuotientData x).isColimit E)
    (Subdivision.domainMap f).hom rfl
  let a := q.isColimit.coconePointUniqueUpToIso hc
  have ha : q.π ≫ a.hom = (E.extensionQuotientData x).π :=
    q.isColimit.comp_coconePointUniqueUpToIso_hom hc WalkingParallelPair.one
  let : Epi q.π := Cofork.IsColimit.epi q.isColimit
  apply QConstruction.mkHom_eq_of_apexIso E.deflation E.inflation _ _ a
  · apply (cancel_epi q.π).1
    simpa only [QConstruction.isoSpan, Category.comp_id, ha] using q.left.symm
  · apply (cancel_epi q.π).1
    change q.π ≫ (a.hom ≫ e.hom) = q.π ≫ (E.extensionProjectionSpan f).r
    rw [← Category.assoc, ha, he, q.right]

end CategoryTheory.ExactCategory.ExactStructure
