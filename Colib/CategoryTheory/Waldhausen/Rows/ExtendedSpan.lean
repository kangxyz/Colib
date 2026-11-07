/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.QSpanNaturality
public import Colib.CategoryTheory.Waldhausen.Rows.ExtendedRows
public import Colib.CategoryTheory.Waldhausen.Rows.RecoverSubobjects
public import Colib.CategoryTheory.Waldhausen.Rows.FlagPresentation


/-! # The terminal Q-span of the reconstructed extended row

The middle quotient, its initial-flag apex and the final quotient are
identified by the actual quotient maps. Under these identifications, the
terminal Q-arrow is represented by the prescribed deflation and inflation.
-/
/- Adapted from the corresponding Quillen Q/S reconstruction source at
   c561118b7795eb9780be9ed391c3251d6a4d0afd. Native Colib objects are retained. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial ZeroObject
universe v u

namespace CategoryTheory.Waldhausen.QuotientRows
open ExactCategory.Filtration

/-- The whole original ordinal as a middle interval in its two-endpoint extension. -/
def extendedMiddleInterval (n : ℕ) : NestedInterval ⦋n + 1 + 1⦌ :=
  ⟨(OrderDual.toDual ((flagMiddleOrdinal n).toOrderHom 0),
    (flagMiddleOrdinal n).toOrderHom (Fin.last n)),
    (flagMiddleOrdinal n).toOrderHom.monotone (Fin.zero_le _)⟩

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : CategoryTheory.ExactCategory.ExactStructure C) {n : ℕ}
variable (A : Fin (n + 1) ⥤ C)
variable (hA : ∀ {i j} (f : i ⟶ j), E.inflation (A.map f))
variable {P Z : C} (p : P ⟶ A.obj (Fin.last n)) (hp : E.deflation p)
variable (r : P ⟶ Z) (hr : E.inflation r)

/-- Quotienting the extended flag by its initial zero recovers the original flag. -/
def extendedRowInitialIso : extendedPullbackFlag E A p hp r ≅
    initialFlag E (extendedRow E A hA p hp r hr) :=
  initialCompletionIso E _ (extendedPullbackFlag_inflation E A p hp r hA hr)
    (isZero_zero C)

/-- The initial comparison retains the specified cokernel projection. -/
@[simp] theorem extendedRowInitialIso_hom_app_eq_flagQuotient (i : Fin (n + 1 + 1 + 1)) :
    (extendedRowInitialIso E A hA p hp r hr).hom.app i =
      flagQuotient E (extendedPullbackFlag E A p hp r)
        (extendedPullbackFlag_inflation E A p hp r hA hr) (interval 0 i (Fin.zero_le _)) := rfl


/-- The terminal initial quotient is canonically the prescribed target. -/
def extendedRowTopIso :
    (initialFlag E (extendedRow E A hA p hp r hr)).obj (Fin.last (n + 1 + 1)) ≅ Z :=
  ((extendedRowInitialIso E A hA p hp r hr).app _).symm ≪≫
    eqToIso (extendedPullbackFlag_obj_last E A p hp r)

/-- The initial quotient at the top middle index is canonically the span apex. -/
def extendedRowApexIso :
    (initialFlag E (extendedRow E A hA p hp r hr)).obj (extendedMiddleInterval n).right ≅ P := by
  letI (i : Fin (n + 1)) : HasPullback p (flagTopMap A i) :=
    flagPullback_exists E A p hp i
  exact ((extendedRowInitialIso E A hA p hp r hr).app _).symm ≪≫
    eqToIso (extendedPullbackFlag_obj_middle E A p hp r (Fin.last n)) ≪≫
      pullbackFlagTopIso A p

/-- The intended admissible representative, with its actual prescribed legs. -/
def extendedRepresentative : Span E.deflation E.inflation
    ((quotientDiagram E A hA).obj (interval 0 (Fin.last n) (Fin.zero_le _))) Z where
  apex := P
  l := p ≫ flagQuotient E A hA (interval 0 (Fin.last n) (Fin.zero_le _))
  r := r
  wl := E.deflation_comp _ _ hp
    (E.deflation_of_conflation (flagQuotient_conflation E hA _))
  wr := hr

/-- The apex identification is inverse to its actual initial quotient map. -/
@[reassoc (attr := simp)] theorem flagQuotient_extendedMiddle_comp_apex [∀ i : Fin (n + 1),
    HasPullback p (flagTopMap A i)] :
    flagQuotient E (extendedPullbackFlag E A p hp r)
      (extendedPullbackFlag_inflation E A p hp r hA hr) (interval 0 (extendedMiddleInterval
          n).right (Fin.zero_le _)) ≫
      (extendedRowApexIso E A hA p hp r hr).hom =
    eqToHom (extendedPullbackFlag_obj_middle E A p hp r (Fin.last n)) ≫
      pullback.fst p (flagTopMap A (Fin.last n)) := by
  change ((extendedRowInitialIso E A hA p hp r hr).app (extendedMiddleInterval n).right).hom ≫
      (extendedRowApexIso E A hA p hp r hr).hom = eqToHom (extendedPullbackFlag_obj_middle E A p
      hp r (Fin.last n)) ≫ pullback.fst p (flagTopMap A (Fin.last n))
  dsimp only [extendedRowApexIso, Iso.trans_hom, Iso.symm_hom]
  rw [Iso.hom_inv_id_assoc]
  rfl


/-- The target identification is inverse to its actual initial quotient map. -/
@[reassoc (attr := simp)] theorem flagQuotient_extendedLast_comp_top :
    flagQuotient E (extendedPullbackFlag E A p hp r)
      (extendedPullbackFlag_inflation E A p hp r hA hr) (interval 0 (Fin.last (n + 1 + 1))
          (Fin.zero_le _)) ≫
      (extendedRowTopIso E A hA p hp r hr).hom =
    eqToHom (extendedPullbackFlag_obj_last E A p hp r) := by
  change ((extendedRowInitialIso E A hA p hp r hr).app (Fin.last (n + 1 + 1))).hom ≫
      (extendedRowTopIso E A hA p hp r hr).hom = eqToHom (extendedPullbackFlag_obj_last E A p hp r)
  dsimp only [extendedRowTopIso, Iso.trans_hom, Iso.symm_hom]
  rw [Iso.hom_inv_id_assoc]
  rfl


/-- The left leg is the prescribed deflation followed by the old quotient map. -/
theorem extendedRow_left_leg :
    (wholeSpan E (extendedRow E A hA p hp r hr) (extendedMiddleInterval n)).l ≫
        (extendedRowMiddleIso E A hA p hp r hr).hom.app
          (interval 0 (Fin.last n) (Fin.zero_le _)) =
      (extendedRowApexIso E A hA p hp r hr).hom ≫
        (extendedRepresentative E A hA p hp r hr).l := by
  let (i : Fin (n + 1)) : HasPullback p (flagTopMap A i) :=
    flagPullback_exists E A p hp i
  let j := (extendedMiddleInterval n).right
  let e := extendedRowInitialIso E A hA p hp r hr
  have hn : (e.app j).hom ≫
      (wholeSpan E (extendedRow E A hA p hp r hr) (extendedMiddleInterval n)).l =
      flagQuotient E (extendedPullbackFlag E A p hp r)
        (extendedPullbackFlag_inflation E A p hp r hA hr)
        (nestedToInterval (extendedMiddleInterval n)) := by
    dsimp only [e, wholeSpan, initialQuotient, extendedRow, flagRow]
    rw [Iso.app_hom, extendedRowInitialIso_hom_app_eq_flagQuotient, flagQuotient_naturality]
    change (extendedPullbackFlag E A p hp r).map (𝟙 j) ≫ _ = _
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  have ht : flagTopMap A (Fin.last n) = 𝟙 _ := A.map_id _
  have hs : pullback.fst p (flagTopMap A (Fin.last n)) ≫ p =
      pullback.snd p (flagTopMap A (Fin.last n)) := by
    simpa only [ht, Category.comp_id] using (pullback.condition (f := p) (g := flagTopMap A
        (Fin.last n)))
  apply (cancel_epi (e.app j).hom).1
  calc
    _ = flagQuotient E (extendedPullbackFlag E A p hp r)
        (extendedPullbackFlag_inflation E A p hp r hA hr)
        (nestedToInterval (extendedMiddleInterval n)) ≫
          (extendedRowMiddleIso E A hA p hp r hr).hom.app
            (interval 0 (Fin.last n) (Fin.zero_le _)) := by rw [← Category.assoc, hn]
    _ = eqToHom (extendedPullbackFlag_obj_middle E A p hp r (Fin.last n)) ≫
        pullback.snd p (flagTopMap A (Fin.last n)) ≫
          flagQuotient E A hA (interval 0 (Fin.last n) (Fin.zero_le _)) :=
      flagQuotient_extendedRowMiddleIso E A hA p hp r hr
        (interval 0 (Fin.last n) (Fin.zero_le _))
    _ = _ := by
      change _ = ((extendedRowInitialIso E A hA p hp r hr).app
        (extendedMiddleInterval n).right).hom ≫
          (extendedRowApexIso E A hA p hp r hr).hom ≫ (p ≫ _)
      rw [Iso.app_hom, extendedRowInitialIso_hom_app_eq_flagQuotient,
    flagQuotient_extendedMiddle_comp_apex_assoc]
      rw [← hs]
      simp only [Category.assoc]

/-- The right leg is the prescribed inflation into the new terminal object. -/
theorem extendedRow_right_leg :
    (wholeSpan E (extendedRow E A hA p hp r hr) (extendedMiddleInterval n)).r ≫
        (extendedRowTopIso E A hA p hp r hr).hom =
      (extendedRowApexIso E A hA p hp r hr).hom ≫ r := by
  let (i : Fin (n + 1)) : HasPullback p (flagTopMap A i) :=
    flagPullback_exists E A p hp i
  let j := (extendedMiddleInterval n).right
  let e := extendedRowInitialIso E A hA p hp r hr
  have hn : (extendedPullbackFlag E A p hp r).map (homOfLE (Fin.le_last j)) ≫
      (e.app (Fin.last (n + 1 + 1))).hom =
    (e.app j).hom ≫
      (wholeSpan E (extendedRow E A hA p hp r hr) (extendedMiddleInterval n)).r :=
    e.hom.naturality (homOfLE (Fin.le_last j))
  apply (cancel_epi (e.app j).hom).1
  rw [← Category.assoc, ← hn, Category.assoc]
  change _ ≫ (((extendedRowInitialIso E A hA p hp r hr).app _).hom ≫
    (extendedRowTopIso E A hA p hp r hr).hom) = _
  rw [Iso.app_hom, extendedRowInitialIso_hom_app_eq_flagQuotient,
    flagQuotient_extendedLast_comp_top]
  change _ = ((extendedRowInitialIso E A hA p hp r hr).app
    (extendedMiddleInterval n).right).hom ≫
      (extendedRowApexIso E A hA p hp r hr).hom ≫ r
  rw [Iso.app_hom, extendedRowInitialIso_hom_app_eq_flagQuotient,
    flagQuotient_extendedMiddle_comp_apex_assoc]
  exact extendedPullbackFlag_middle_to_last E A p hp r (Fin.last n)

/-- The actual final Q-arrow of the extension has the prescribed representative,
under its explicit middle-source and terminal-target identifications. -/
theorem extendedRow_wholeSpan :
    QConstruction.mkHom E.deflation E.inflation
        (wholeSpan E (extendedRow E A hA p hp r hr) (extendedMiddleInterval n)) ≫
      (E.qIsoOfIso (extendedRowTopIso E A hA p hp r hr)).hom =
    (E.qIsoOfIso ((extendedRowMiddleIso E A hA p hp r hr).app
        (interval 0 (Fin.last n) (Fin.zero_le _)))).hom ≫
      QConstruction.mkHom E.deflation E.inflation (extendedRepresentative E A hA p hp r hr) :=
  E.qSpan_iso_naturality _ _ _ _ (extendedRowApexIso E A hA p hp r hr)
    (extendedRow_left_leg E A hA p hp r hr) (extendedRow_right_leg E A hA p hp r hr)

/-- For an existing row, completing its initial flag recovers the prescribed
left leg itself, under the canonical cokernel identification. -/
theorem extendedRepresentative_initialFlag (F : Obj (ofExactCategory E) ⦋n⦌) {P Z : C}
    (p : P ⟶ (initialFlag E F).obj (Fin.last n)) (hp : E.deflation p)
    (r : P ⟶ Z) (hr : E.inflation r) :
    QConstruction.mkHom E.deflation E.inflation
      (extendedRepresentative E (initialFlag E F) (initialFlag_inflation E F) p hp r hr) =
    (E.qIsoOfIso ((completedInitialIso E F).app
      (interval 0 (Fin.last n) (Fin.zero_le _)))).hom ≫
      QConstruction.mkHom E.deflation E.inflation
        ({ apex := P, l := p, r := r, wl := hp, wr := hr } :
          Span E.deflation E.inflation ((initialFlag E F).obj (Fin.last n)) Z) := by
  have h := E.qSpan_iso_naturality
    (extendedRepresentative E (initialFlag E F) (initialFlag_inflation E F) p hp r hr)
    ({ apex := P, l := p, r := r, wl := hp, wr := hr } :
      Span E.deflation E.inflation ((initialFlag E F).obj (Fin.last n)) Z)
    ((completedInitialIso E F).app (interval 0 (Fin.last n) (Fin.zero_le _)))
    (Iso.refl Z) (Iso.refl P) (by
      have hl : flagQuotient E (initialFlag E F) (initialFlag_inflation E F)
          (interval 0 (Fin.last n) (Fin.zero_le _)) ≫
          (completedInitialIsoAt E F (interval 0 (Fin.last n) (Fin.zero_le _))).hom = 𝟙 _ :=
        (flagQuotient_completedInitialIsoAt E F _).trans (initialQuotient_initial E F _)
      change (p ≫ flagQuotient E (initialFlag E F) (initialFlag_inflation E F)
          (interval 0 (Fin.last n) (Fin.zero_le _))) ≫
          (completedInitialIsoAt E F (interval 0 (Fin.last n) (Fin.zero_le _))).hom = 𝟙 P ≫ p
      exact (Category.assoc _ _ _).trans ((congrArg (fun f ↦ p ≫ f) hl).trans
        ((Category.comp_id p).trans (Category.id_comp p).symm)))
      (by change r ≫ 𝟙 Z = 𝟙 P ≫ r
          exact (Category.comp_id r).trans (Category.id_comp r).symm)
  simpa using h

end CategoryTheory.Waldhausen.QuotientRows
