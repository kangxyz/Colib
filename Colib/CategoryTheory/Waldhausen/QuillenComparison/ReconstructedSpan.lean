/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.QuillenComparison.ReconstructedRows
public import Colib.CategoryTheory.Waldhausen.Rows.ExtendedSpan
public import Colib.CategoryTheory.Waldhausen.QuillenComparison.IntervalTransport


/-! # The terminal arrow of the recursively reconstructed Q-chain -/
/- Adapted from the corresponding Quillen Q/S reconstruction source at
   c561118b7795eb9780be9ed391c3251d6a4d0afd. Native Colib objects are retained. -/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe v u

namespace CategoryTheory.Waldhausen.QuillenComparison
open QuotientRows SSet ExactCategory.Filtration

/-- The penultimate central interval is precisely the whole old middle row. -/
theorem reconstructionOrdinalCast_penultimate (n : ℕ) :
    (nestedIntervalMap (reconstructionOrdinalCast n)).obj
      (centralInterval ⦋n + 1⦌ (Fin.last n).castSucc) =
      extendedMiddleInterval (EdgewiseSubdivision.ε.obj ⦋n⦌).len := by
  rw [← reconstructionMiddleOrdinal_central]
  change (nestedIntervalMap (reconstructionMiddleOrdinal n ≫ reconstructionOrdinalCast n)).obj
    (centralInterval ⦋n⦌ (Fin.last n)) = _
  rw [reconstructionMiddle_comp_cast, centralInterval_last]
  rfl

/-- The final central interval remains the whole row under the ordinal cast. -/
theorem reconstructionOrdinalCast_last (n : ℕ) :
    (nestedIntervalMap (reconstructionOrdinalCast n)).obj
      (centralInterval ⦋n + 1⦌ (Fin.last (n + 1))) =
      topNested ⦋(EdgewiseSubdivision.ε.obj ⦋n⦌).len + 1 + 1⦌ := by
  rw [centralInterval_last]
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext
  · exact reconstructionOrdinalCast_val n 0
  · rw [show ((nestedIntervalMap (reconstructionOrdinalCast n)).obj
        (topNested (EdgewiseSubdivision.ε.obj ⦋n + 1⦌))).1.2 =
      (reconstructionOrdinalCast n).toOrderHom (Fin.last (EdgewiseSubdivision.ε.obj ⦋n + 1⦌).len)
        from rfl]
    rw [reconstructionOrdinalCast_val]
    change (n + 1) + (n + 1) + 1 = n + n + 1 + 1 + 1
    omega

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C)

@[simp]
theorem rowReindexEqIso_hom_app {a b : SimplexCategory} {α β : a ⟶ b} (h : α = β)
    (G : Obj (ofExactCategory E) b) (ij : Interval a) :
    (rowReindexEqIso E h G).hom.app ij =
      eqToHom (congrArg (fun γ ↦ G.obj.obj ((indexMap γ).obj ij)) h) := by
  subst β
  rfl

omit [Preadditive C] [HasFiniteBiproducts C] in
private theorem iso_app_transport {I : Type*} [Category I] {A B : I ⥤ C}
    (e : A ≅ B) {i j : I} (h : i = j) :
    (e.app i).hom ≫ eqToHom (congrArg B.obj h) =
      eqToHom (congrArg A.obj h) ≫ (e.app j).hom := by
  subst j
  simp

variable {n : ℕ} (F : Obj (ofExactCategory E) (EdgewiseSubdivision.ε.obj ⦋n⦌))
variable {P Z : C} (p : P ⟶ (initialFlag E F).obj (Fin.last (EdgewiseSubdivision.ε.obj ⦋n⦌).len))
  (hp : E.deflation p) (r : P ⟶ Z) (hr : E.inflation r)

/-- The final central quotient of the reconstructed row is the prescribed new target. -/
def reconstructedTopIso :
    (reconstructedRow E F p hp r hr).obj.obj
        (nestedToInterval (centralInterval ⦋n + 1⦌ (Fin.last (n + 1)))) ≅ Z :=
  eqToIso (congrArg (fun k ↦
    (extendedRow E (initialFlag E F) (initialFlag_inflation E F) p hp r hr).obj.obj
      (nestedToInterval k)) (reconstructionOrdinalCast_last n)) ≪≫
    extendedRowTopIso E (initialFlag E F) (initialFlag_inflation E F) p hp r hr

/-- The penultimate source cast to the literal whole middle interval. -/
def reconstructedPenultimateIso :
    (reconstructedRow E F p hp r hr).obj.obj
        (nestedToInterval (centralInterval ⦋n + 1⦌ (Fin.last n).castSucc)) ≅
      (extendedRow E (initialFlag E F) (initialFlag_inflation E F) p hp r hr).obj.obj
        (nestedToInterval (extendedMiddleInterval (EdgewiseSubdivision.ε.obj ⦋n⦌).len)) :=
  eqToIso (congrArg (fun k ↦
    (extendedRow E (initialFlag E F) (initialFlag_inflation E F) p hp r hr).obj.obj
      (nestedToInterval k)) (reconstructionOrdinalCast_penultimate n))

/-- Before the original-row source identification, the terminal Q-arrow is the
actual whole-span of the literal extended row, with exactly the ordinal casts. -/
theorem reconstructedRow_last_step_to_whole :
    (((rowChainComparison E ⦋n + 1⦌).obj ⟨reconstructedRow E F p hp r hr⟩).of.map
        (homOfLE (Fin.le_last (Fin.last n).castSucc))) ≫
      (E.qIsoOfIso (reconstructedTopIso E F p hp r hr)).hom =
    (E.qIsoOfIso (reconstructedPenultimateIso E F p hp r hr)).hom ≫
      QConstruction.mkHom E.deflation E.inflation
        (wholeSpan E
          (extendedRow E (initialFlag E F) (initialFlag_inflation E F) p hp r hr)
          (extendedMiddleInterval (EdgewiseSubdivision.ε.obj ⦋n⦌).len)) ≫
        (E.qIsoOfIso (extendedRowTopIso E (initialFlag E F) (initialFlag_inflation E F)
          p hp r hr)).hom := by
  let a := (centralIntervalFunctor ⦋n + 1⦌).map
    (homOfLE (Fin.le_last (Fin.last n).castSucc))
  have h := rowInterval_map_to_whole E
    (extendedRow E (initialFlag E F) (initialFlag_inflation E F) p hp r hr)
    ((nestedIntervalMap (reconstructionOrdinalCast n)).map a)
    (extendedMiddleInterval (EdgewiseSubdivision.ε.obj ⦋n⦌).len)
    (reconstructionOrdinalCast_penultimate n) (reconstructionOrdinalCast_last n)
  change _ ≫ (E.qIsoOfIso (_ ≪≫ _)).hom = _
  rw [CategoryTheory.ExactCategory.ExactStructure.qIsoOfIso_trans, Iso.trans_hom, ← Category.assoc]
  simpa only [Category.assoc] using! congrArg (fun f ↦ f ≫
    (E.qIsoOfIso (extendedRowTopIso E (initialFlag E F)
      (initialFlag_inflation E F) p hp r hr)).hom) h

/-- The reconstructed old terminal component agrees with the literal middle
identification after the canonical original-row top identification. -/
theorem reconstructedCentralIsoAt_last_top :
    reconstructedCentralIsoAt E F p hp r hr (Fin.last n) ≪≫ centralTopIso E F =
      reconstructedPenultimateIso E F p hp r hr ≪≫
        (extendedRowMiddleIso E (initialFlag E F) (initialFlag_inflation E F) p hp r hr).app
          (interval 0 (Fin.last (EdgewiseSubdivision.ε.obj ⦋n⦌).len) (Fin.zero_le _)) ≪≫
        (completedInitialIso E F).app
          (interval 0 (Fin.last (EdgewiseSubdivision.ε.obj ⦋n⦌).len) (Fin.zero_le _)) := by
  let R := extendedRow E (initialFlag E F) (initialFlag_inflation E F) p hp r hr
  let e := extendedRowMiddleIso E (initialFlag E F) (initialFlag_inflation E F) p hp r hr ≪≫
    completedInitialIso E F
  let ij := nestedToInterval (centralInterval ⦋n⦌ (Fin.last n))
  let c := eqToIso (congrArg (fun q ↦ (reconstructedRow E F p hp r hr).obj.obj
    (nestedToInterval q)) (reconstructionMiddleOrdinal_central n (Fin.last n)).symm)
  have hij : ij = interval 0 (Fin.last (EdgewiseSubdivision.ε.obj ⦋n⦌).len) (Fin.zero_le _) := by
    dsimp only [ij]
    rw [centralInterval_last, nestedToInterval_topNested_edgewise]
  have h := congrArg (fun t ↦ c.hom ≫
    (rowReindexEqIso E (reconstructionMiddle_comp_cast n) R).hom.app ij ≫ t)
      (iso_app_transport e hij)
  apply Iso.ext
  simpa only [c, e, R, ij, reconstructedCentralIsoAt, reconstructedPenultimateIso,
    centralTopIso, reconstructedMiddleIso, rowReindexCompIso, reconstructedRow, reindex,
    Functor.comp_obj, Iso.trans_hom, Iso.app_hom,
    NatTrans.comp_app, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    rowReindexEqIso_hom_app, eqToIso.hom, Category.assoc, eqToHom_trans_assoc] using! h

/-- The actual final adjacent Q-arrow of the reconstructed chain has exactly
the prescribed span after the displayed source and target identifications. -/
theorem reconstructedRow_last_step :
    ComposableArrows.map' ((rowChainComparison E ⦋n + 1⦌).obj
        ⟨reconstructedRow E F p hp r hr⟩).of n (n + 1) ≫
      (E.qIsoOfIso (reconstructedTopIso E F p hp r hr)).hom =
    (reconstructedInitialChainIso E F p hp r hr).hom.app (Fin.last n) ≫
      (E.qIsoOfIso (centralTopIso E F)).hom ≫
        QConstruction.mkHom E.deflation E.inflation
          ({ apex := P, l := p, r := r, wl := hp, wr := hr } :
            Span E.deflation E.inflation
              ((initialFlag E F).obj (Fin.last (EdgewiseSubdivision.ε.obj ⦋n⦌).len)) Z) := by
  let s : Span E.deflation E.inflation
      ((initialFlag E F).obj (Fin.last (EdgewiseSubdivision.ε.obj ⦋n⦌).len)) Z :=
    { apex := P, l := p, r := r, wl := hp, wr := hr }
  have hc := congrArg (fun e ↦ (E.qIsoOfIso e).hom)
    (reconstructedCentralIsoAt_last_top E F p hp r hr)
  simp only [CategoryTheory.ExactCategory.ExactStructure.qIsoOfIso_trans, Iso.trans_hom] at hc
  have hi := congrArg Iso.hom (reconstructedInitialChainIso_app_last E F p hp r hr)
  have he : (reconstructedInitialChainIso E F p hp r hr).hom.app (Fin.last n) ≫
      (E.qIsoOfIso (centralTopIso E F)).hom =
    (E.qIsoOfIso (reconstructedPenultimateIso E F p hp r hr)).hom ≫
      (E.qIsoOfIso ((extendedRowMiddleIso E (initialFlag E F) (initialFlag_inflation E F)
        p hp r hr).app (interval 0 (Fin.last (EdgewiseSubdivision.ε.obj ⦋n⦌).len) (Fin.zero_le
          _)))).hom ≫
      (E.qIsoOfIso ((completedInitialIso E F).app
        (interval 0 (Fin.last (EdgewiseSubdivision.ε.obj ⦋n⦌).len) (Fin.zero_le _)))).hom :=
    (congrArg (fun k ↦ k ≫ (E.qIsoOfIso (centralTopIso E F)).hom) hi).trans hc
  calc
    _ = (E.qIsoOfIso (reconstructedPenultimateIso E F p hp r hr)).hom ≫
        QConstruction.mkHom E.deflation E.inflation
          (wholeSpan E (extendedRow E (initialFlag E F) (initialFlag_inflation E F) p hp r hr)
            (extendedMiddleInterval (EdgewiseSubdivision.ε.obj ⦋n⦌).len)) ≫
          (E.qIsoOfIso (extendedRowTopIso E (initialFlag E F) (initialFlag_inflation E F)
            p hp r hr)).hom := reconstructedRow_last_step_to_whole E F p hp r hr
    _ = _ := by
      rw [extendedRow_wholeSpan, extendedRepresentative_initialFlag]
      simpa only [Category.assoc] using!
        (congrArg (fun k ↦ k ≫ QConstruction.mkHom E.deflation E.inflation s) he).symm

end CategoryTheory.Waldhausen.QuillenComparison
