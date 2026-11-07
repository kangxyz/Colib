/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Rows.FlagReindexing
public import Colib.CategoryTheory.ExactCategory.Filtration.FlagExtension
public import Colib.CategoryTheory.Waldhausen.Rows.PullbackQuotients


/-! # Exact rows reconstructed by pullback and two endpoint extensions -/
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
open ExactCategory.Filtration

/-- The middle embedding of an ordinal after adding one endpoint on each side. -/
def flagMiddleOrdinal (n : ℕ) : ⦋n⦌ ⟶ ⦋n + 1 + 1⦌ :=
  SimplexCategory.Hom.mk ⟨fun i ↦ i.castSucc.succ, fun _ _ h ↦ Fin.succ_le_succ_iff.mpr h⟩

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : CategoryTheory.ExactCategory.ExactStructure C) {n : ℕ}
variable (A : Fin (n + 1) ⥤ C)
variable (hA : ∀ {i j} (f : i ⟶ j), E.inflation (A.map f))
variable {P Z : C} (p : P ⟶ A.obj (Fin.last n)) (hp : E.deflation p)
variable (r : P ⟶ Z) (hr : E.inflation r)

/-- An actual exact row obtained from the pullback flag and its two endpoints. -/
def extendedRow : Obj (ofExactCategory E) ⦋n + 1 + 1⦌ :=
  flagRow E (extendedPullbackFlag E A p hp r)
    (extendedPullbackFlag_inflation E A p hp r hA hr)

/-- Its restriction to the middle interval canonically recovers the original
completed flag. All pullbacks are provided by admissibility of the left leg. -/
def extendedRowMiddleIso :
    ((reindex (ofExactCategory E) (flagMiddleOrdinal n)).obj (extendedRow E A hA p hp r hr)).obj ≅
      (flagRow E A hA).obj := by
  letI (i : Fin (n + 1)) : HasPullback p (flagTopMap A i) :=
    flagPullback_exists E A p hp i
  exact quotientNatIso E
      (fun f ↦ extendedPullbackFlag_inflation E A p hp r hA hr
        ((Fin.castSuccFunctor (n + 1) ⋙ Fin.succFunctor (n + 1 + 1)).map f))
      (pullbackFlag_inflation E A p hp hA)
      (extendedPullbackFlagMiddleIso E A p hp r) ≪≫
      pullbackFlagQuotientIso E A hA p hp

variable [∀ i : Fin (n + 1), HasPullback p (flagTopMap A i)]

/-- The middle identification is exactly the map on cokernels induced by
pullback projection; it is not an unspecified choice of row isomorphism. -/
@[reassoc (attr := simp)]
theorem flagQuotient_extendedRowMiddleIso (ij : Interval ⦋n⦌) :
    flagQuotient E (extendedPullbackFlag E A p hp r)
        (extendedPullbackFlag_inflation E A p hp r hA hr)
        ((indexMap (flagMiddleOrdinal n)).obj ij) ≫
      (extendedRowMiddleIso E A hA p hp r hr).hom.app ij =
      eqToHom (extendedPullbackFlag_obj_middle E A p hp r ij.1.2) ≫
        pullback.snd p (flagTopMap A ij.1.2) ≫ flagQuotient E A hA ij := by
  change flagQuotient E
      ((Fin.castSuccFunctor (n + 1) ⋙ Fin.succFunctor (n + 1 + 1)) ⋙
        extendedPullbackFlag E A p hp r)
      (fun f ↦ extendedPullbackFlag_inflation E A p hp r hA hr
        ((Fin.castSuccFunctor (n + 1) ⋙ Fin.succFunctor (n + 1 + 1)).map f)) ij ≫ _ = _
  dsimp only [extendedRowMiddleIso, Iso.trans_hom, NatTrans.comp_app,
    flagRowReindexIso, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    quotientNatIso, pullbackFlagQuotientIso, NatIso.ofComponents_hom_app, asIso_hom]
  rw [flagQuotient_quotientNatTrans_assoc, flagQuotient_quotientNatTrans]
  rfl

end CategoryTheory.Waldhausen.QuotientRows
