/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.Composition
public import Colib.CategoryTheory.ExactCategory.Isomorphisms
public import Colib.CategoryTheory.QConstruction.Basic

/-!
Implementation provenance:
`Quillen/CategoryTheory/ExactCategory/ExtensionQuotientSpan.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Actual quotient spans from nested admissible subobjects

For `A' ↪ A ↪ B ↪ B'`, the quotient span is `B/A ← B/A' ↪ B'/A'`.
Both admissibility assertions are derived by pushout and cokernel universal
properties in the original exact category.
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

/-- Construct the original admissible Q span from three nested subobjects and
actual quotient conflations. No cokernels beyond those provided by exactness
are assumed to exist. -/
def quotientSpanOfInflations {A' A B B' H X Y : C}
    (h : A' ⟶ A) (i : A ⟶ B) (k : B ⟶ B')
    (pH : A ⟶ H) (pX : B ⟶ X) (pY : B' ⟶ Y)
    (zH : h ≫ pH = 0) (zX : i ≫ pX = 0) (zY : (h ≫ i) ≫ k ≫ pY = 0)
    (cH : E.conflation (ShortComplex.mk h pH zH))
    (cX : E.conflation (ShortComplex.mk i pX zX))
    (cY : E.conflation (ShortComplex.mk ((h ≫ i) ≫ k) pY (by
      simpa only [Category.assoc] using zY)))
    (hk : E.inflation k) : Span E.deflation E.inflation X Y := by
  let hi := E.inflation_of_conflation cX
  letI : HasPushout i pH := E.inflation.hasPushout pH hi
  have cM := E.composite_inflation_conflation cH cX
  let q := pushout.inl i pH
  let l := pushout.desc (f := i) (g := pH) pX 0 (by simpa using zX)
  have hl : E.deflation l := E.deflation_of_conflation (E.pushoutConflation_mem cX pH)
  have zM : (h ≫ i) ≫ q = 0 := by
    dsimp [q]
    rw [Category.assoc, pushout.condition, ← Category.assoc, zH, zero_comp]
  let hcM := E.cokernel (ShortComplex.mk (h ≫ i) q zM) cM
  let r := hcM.desc (CokernelCofork.ofπ (k ≫ pY) zY)
  have qr : q ≫ r = k ≫ pY := hcM.fac _ WalkingParallelPair.one
  have hr : E.inflation r := by
    let : HasPushout k q := E.inflation.hasPushout q hk
    obtain ⟨K, pK, zK, cK⟩ := hk
    have cN := E.composite_inflation_conflation cM cK
    let hcY := E.cokernel (ShortComplex.mk ((h ≫ i) ≫ k) pY
      (by simpa only [Category.assoc] using zY)) cY
    let e := (E.cokernel _ cN).coconePointUniqueUpToIso hcY
    have he : pushout.inl k q ≫ e.hom = pY :=
      (E.cokernel _ cN).comp_coconePointUniqueUpToIso_hom
        hcY WalkingParallelPair.one
    have hq : E.deflation q := E.deflation_of_conflation cM
    let : Epi q := E.epi_of_deflation hq
    have re : r = pushout.inr k q ≫ e.hom := by
      apply (cancel_epi q).1
      rw [qr, ← Category.assoc, ← pushout.condition, Category.assoc, he]
    rw [re]
    exact E.inflation_comp _ _
      (E.inflation.pushout_inr _ _ (E.inflation_of_conflation cK)) (E.inflation_of_iso e)
  exact ⟨pushout i pH, l, r, hl, hr⟩

end CategoryTheory.ExactCategory.ExactStructure
