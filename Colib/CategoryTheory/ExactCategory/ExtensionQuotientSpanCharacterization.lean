/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.ExtensionQuotientSpan

/-!
Implementation provenance:
`Quillen/CategoryTheory/ExactCategory/ExtensionQuotientSpanCharacterization.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Universal characterization of extension quotient spans

The middle object is the actual cokernel of the smaller subobject. Its two
span legs are characterized by their composites with that cokernel map.
-/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ExactCategory.ExactStructure.QuotientSpan
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C) {A' A B B' H X Y : C}
variable (h : A' ⟶ A) (i : A ⟶ B) (k : B ⟶ B')
variable (pH : A ⟶ H) (pX : B ⟶ X) (pY : B' ⟶ Y)
variable (zH : h ≫ pH = 0) (zX : i ≫ pX = 0) (zY : (h ≫ i) ≫ k ≫ pY = 0)
variable (cH : E.conflation (ShortComplex.mk h pH zH))
variable (cX : E.conflation (ShortComplex.mk i pX zX))
variable (cY : E.conflation (ShortComplex.mk ((h ≫ i) ≫ k) pY
  ((Category.assoc (h ≫ i) k pY).trans zY))) (hk : E.inflation k)

local notation "s" => E.quotientSpanOfInflations h i k pH pX pY zH zX zY cH cX cY hk

/-- The actual quotient map to the middle object of the span. -/
def projection : B ⟶ (s).apex := by
  letI : HasPushout i pH := E.inflation.hasPushout pH (E.inflation_of_conflation cX)
  exact pushout.inl i pH

local notation "q" => projection E h i k pH pX pY zH zX zY cH cX cY hk

@[reassoc (attr := simp)]
theorem projection_left : q ≫ (s).l = pX := by
  dsimp [projection, quotientSpanOfInflations]
  simp

@[reassoc (attr := simp)]
theorem projection_right : q ≫ (s).r = k ≫ pY := by
  let : HasPushout i pH := E.inflation.hasPushout pH (E.inflation_of_conflation cX)
  dsimp [projection, quotientSpanOfInflations]
  exact (E.cokernel _ (E.composite_inflation_conflation cH cX)).fac
    (CokernelCofork.ofπ (k ≫ pY) zY) WalkingParallelPair.one

@[reassoc]
theorem projection_zero : (h ≫ i) ≫ q = 0 := by
  let : HasPushout i pH := E.inflation.hasPushout pH (E.inflation_of_conflation cX)
  dsimp [projection, quotientSpanOfInflations]
  rw [Category.assoc, pushout.condition, ← Category.assoc, zH, zero_comp]

/-- The span middle object really is the smaller-subobject quotient. -/
def projectionIsCokernel :
    IsColimit (CokernelCofork.ofπ q
      (projection_zero E h i k pH pX pY zH zX zY cH cX cY hk)) := by
  letI : HasPushout i pH := E.inflation.hasPushout pH (E.inflation_of_conflation cX)
  exact E.cokernel _ (E.composite_inflation_conflation cH cX)

/-- Any other cokernel presentation with the prescribed two composites gives
exactly the same arrow in the original Q quotient. -/
theorem mkHom_eq_of_cokernel (t : Span E.deflation E.inflation X Y)
    (p : B ⟶ t.apex) (zp : (h ≫ i) ≫ p = 0)
    (hp : IsColimit (CokernelCofork.ofπ p zp))
    (pl : p ≫ t.l = pX) (pr : p ≫ t.r = k ≫ pY) :
    QConstruction.mkHom E.deflation E.inflation s =
      QConstruction.mkHom E.deflation E.inflation t := by
  let hc := projectionIsCokernel E h i k pH pX pY zH zX zY cH cX cY hk
  let e := hc.coconePointUniqueUpToIso hp
  have he : q ≫ e.hom = p :=
    hc.comp_coconePointUniqueUpToIso_hom hp WalkingParallelPair.one
  let : Epi q := Cofork.IsColimit.epi hc
  apply QConstruction.mkHom_eq_of_apexIso E.deflation E.inflation s t e
  · apply (cancel_epi q).1
    rw [← Category.assoc, he, pl, projection_left]
  · apply (cancel_epi q).1
    rw [← Category.assoc, he, pr, projection_right]

end CategoryTheory.ExactCategory.ExactStructure.QuotientSpan
