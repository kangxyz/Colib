/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Rows.AdmissibleFlags


/-! # Arbitrary maps between completed admissible flags

Completion is functorial for actual natural transformations of flags, not
only for isomorphisms. This is also the input needed to transport weak
equivalences between finite filtrations in a complex category.
-/
/- Adapted from the corresponding Quillen Q/S reconstruction source at
   c561118b7795eb9780be9ed391c3251d6a4d0afd. Native Colib objects are retained. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe v u

namespace CategoryTheory.Waldhausen.QuotientRows

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : CategoryTheory.ExactCategory.ExactStructure C) {n : SimplexCategory}
variable {A B : Fin (n.len + 1) ⥤ C}
variable (hA : ∀ {i j} (f : i ⟶ j), E.inflation (A.map f))
variable (hB : ∀ {i j} (f : i ⟶ j), E.inflation (B.map f))

/-- A natural transformation of admissible flags induces the natural
transformation between all their actual interval cokernels. -/
def quotientNatTrans (η : A ⟶ B) : quotientDiagram E A hA ⟶ quotientDiagram E B hB := by
  letI {i j : Fin (n.len + 1)} (f : i ⟶ j) : HasCokernel (A.map f) :=
    E.hasCokernel_of_inflation (A.map f) (hA f)
  letI {i j : Fin (n.len + 1)} (f : i ⟶ j) : HasCokernel (B.map f) :=
    E.hasCokernel_of_inflation (B.map f) (hB f)
  exact {
    app p := cokernel.map (A.map (homOfLE p.2)) (B.map (homOfLE p.2))
      (η.app p.1.1) (η.app p.1.2) (η.naturality _)
    naturality {p q} f := by
      apply (cancel_epi (flagQuotient E A hA p)).1
      change cokernel.π _ ≫ (_ ≫ _) = cokernel.π _ ≫ (_ ≫ _)
      simp only [quotientDiagram, cokernel.map, cokernel.π_desc_assoc, Category.assoc,
        cokernel.π_desc]
      rw [← Category.assoc, η.naturality, Category.assoc] }

@[reassoc (attr := simp)]
theorem flagQuotient_quotientNatTrans (η : A ⟶ B) (p : Interval n) :
    flagQuotient E A hA p ≫ (quotientNatTrans E hA hB η).app p =
      η.app p.1.2 ≫ flagQuotient E B hB p := by
  let {i j : Fin (n.len + 1)} (f : i ⟶ j) : HasCokernel (A.map f) :=
    E.hasCokernel_of_inflation (A.map f) (hA f)
  let {i j : Fin (n.len + 1)} (f : i ⟶ j) : HasCokernel (B.map f) :=
    E.hasCokernel_of_inflation (B.map f) (hB f)
  exact cokernel.π_desc _ _ _

/-- The original flag inclusion is killed by its actual quotient map. -/
@[reassoc (attr := simp)]
theorem flagQuotient_zero (p : Interval n) :
    A.map (homOfLE p.2) ≫ flagQuotient E A hA p = 0 := by
  let {i j : Fin (n.len + 1)} (f : i ⟶ j) : HasCokernel (A.map f) :=
    E.hasCokernel_of_inflation (A.map f) (hA f)
  exact cokernel.condition _

/-- The completed row retains its original defining cokernel universal property. -/
def flagQuotientIsCokernel (p : Interval n) :
    IsColimit (CokernelCofork.ofπ (flagQuotient E A hA p) (flagQuotient_zero E hA p)) := by
  letI {i j : Fin (n.len + 1)} (f : i ⟶ j) : HasCokernel (A.map f) :=
    E.hasCokernel_of_inflation (A.map f) (hA f)
  exact cokernelIsCokernel _

/-- Every flag inclusion and its completed quotient form an actual conflation. -/
theorem flagQuotient_conflation (p : Interval n) :
    E.conflation (ShortComplex.mk (A.map (homOfLE p.2)) (flagQuotient E A hA p)
      (flagQuotient_zero E hA p)) :=
  E.conflation_of_inflation_of_isCokernel (hA _) (flagQuotientIsCokernel E hA p)

@[simp]
theorem quotientNatTrans_id : quotientNatTrans E hA hA (𝟙 A) = 𝟙 _ := by
  ext p
  let : Epi (flagQuotient E A hA p) := inferInstance
  apply (cancel_epi (flagQuotient E A hA p)).1
  rw [flagQuotient_quotientNatTrans]
  simp

@[simp]
theorem quotientNatTrans_comp {T : Fin (n.len + 1) ⥤ C}
    (hT : ∀ {i j} (f : i ⟶ j), E.inflation (T.map f)) (η : A ⟶ B) (θ : B ⟶ T) :
    quotientNatTrans E hA hT (η ≫ θ) = quotientNatTrans E hA hB η ≫ quotientNatTrans E hB hT θ := by
  ext p
  let : Epi (flagQuotient E A hA p) := inferInstance
  apply (cancel_epi (flagQuotient E A hA p)).1
  simp only [NatTrans.comp_app, flagQuotient_quotientNatTrans, flagQuotient_quotientNatTrans_assoc,
    Category.assoc]

/-- An isomorphism of flags induces the expected isomorphism of completed rows. -/
def quotientNatIso (e : A ≅ B) : quotientDiagram E A hA ≅ quotientDiagram E B hB where
  hom := quotientNatTrans E hA hB e.hom
  inv := quotientNatTrans E hB hA e.inv
  hom_inv_id := by rw [← quotientNatTrans_comp, e.hom_inv_id, quotientNatTrans_id]
  inv_hom_id := by rw [← quotientNatTrans_comp, e.inv_hom_id, quotientNatTrans_id]

end CategoryTheory.Waldhausen.QuotientRows
