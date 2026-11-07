/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.Waldhausen.Approximation.GeneralKEquivalence
import Colib.CategoryTheory.Waldhausen.Rows.InitialFlag

/-! Regression checks for the original maps and independent object/hom universes. -/

noncomputable section

open CategoryTheory CategoryTheory.Waldhausen Topology

universe u v

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}
  (h : HasApproximationProperty W V F)
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  [V.weq.HasTwoOutOfThreeProperty]
  (J : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl W))

example : IsWeakHomotopyEquivalence (deloopingMap hF).hom :=
  h.deloopingMap_isWeakHomotopyEquivalence_general hF J

example (n : ℕ) : Function.Bijective (KMap hF n) := h.KMap_bijective_general hF J n

example : W.K 0 ≃* V.K 0 := h.KEquivGeneral hF J 0

example (n : ℕ) : (↑(h.KEquivGeneral hF J n) : W.K n →* V.K n) = KMap hF n := rfl

example (n : SimplexCategory) :
    HasApproximationProperty (QuotientRows.waldhausenStructure W n)
      (QuotientRows.waldhausenStructure V n) (QuotientRows.postcompose W V hF n) :=
  h.row_approximation_of_joint hF J n

section InitialQuotients

variable [Preadditive C] [Limits.HasFiniteBiproducts C]
  (E : ExactCategory.ExactStructure C) {n : SimplexCategory}
  (A : QuotientRows.Obj (ofExactCategory E) n)

example : QuotientRows.initialFlag E A =
    (QuotientRows.initialFlagFunctor (ofExactCategory E) n).obj A := rfl

example (p : Interval n) :
    (QuotientRows.initialQuotient (ofExactCategory E) A p :
      (QuotientRows.initialFlag E A).obj p.1.2 ⟶ A.obj.obj p) =
        A.obj.map (homOfLE (show interval 0 p.1.2 (Fin.zero_le _) ≤ p from
          ⟨Fin.zero_le _, le_rfl⟩)) := rfl

end InitialQuotients
