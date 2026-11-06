/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

import Colib.KTheory.Quillen.Localization.Serre.FiberEquivalence

/-! Regressions for the canonical comparison, its zero-degree case, its actual
forward homomorphism and its arbitrary-basepoint weak equivalence. -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory Topology
open CategoryTheory.ExactCategory.SerreLocalization
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts canonicalQuotientAbelian

variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

example (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n)
      (basedLocalizationFiberComparison P) (basedLocalizationFiberComparison_basepoint P)) :=
  basedLocalizationFiberComparison_bijective P n

example :
    Function.Bijective (HomotopyGroup.map (N := Fin 0)
      (basedLocalizationFiberComparison P) (basedLocalizationFiberComparison_basepoint P)) :=
  basedLocalizationFiberComparison_bijective P 0

example (n : ℕ) : Function.Bijective (localizationFiberComparisonHom P n) :=
  localizationFiberComparisonHom_bijective P n

example (n : ℕ) (a : (abelianExactStructure P.FullSubcategory).K n) :
    localizationFiberEquiv P n a = HomotopyGroup.map (N := Fin (n + 1))
      (basedLocalizationFiberComparison P) (basedLocalizationFiberComparison_basepoint P) a := rfl

example (n : ℕ) :
    (↑(localizationFiberEquiv P n) : (abelianExactStructure P.FullSubcategory).K n →*
      HomotopyGroup.Pi (n + 1) (NormalizedLocalizationFiber P) (normalizedFiberBasepoint P)) =
        localizationFiberComparisonHom P n := rfl

example (n : ℕ) :
    (localizationFiberProjectionHom P n).comp (localizationFiberEquiv P n).toMonoidHom =
      Abelian.Devissage.KMap P n :=
  localizationFiberComparisonHom_projection P n

example (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (NormalizedLocalizationFiber P) (normalizedFiberBasepoint P)) :
    localizationFiberComparisonHom P n ((localizationFiberEquiv P n).symm a) = a :=
  (localizationFiberEquiv P n).apply_symm_apply a

example (n : ℕ) (a : (abelianExactStructure P.FullSubcategory).K n) :
    (localizationFiberEquiv P n).symm (localizationFiberComparisonHom P n a) = a :=
  (localizationFiberEquiv P n).symm_apply_apply a

example : IsWeakHomotopyEquivalence (basedLocalizationFiberComparison P) :=
  basedLocalizationFiberComparison_isWeakHomotopyEquivalence P

example (x : (abelianExactStructure P.FullSubcategory).KSpace) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n)
      (basedLocalizationFiberComparison P) (x := x) rfl) :=
  (basedLocalizationFiberComparison_isWeakHomotopyEquivalence P).homotopy_bijective x n

example (y : NormalizedLocalizationFiber P) :
    ∃ x : (abelianExactStructure P.FullSubcategory).KSpace,
      Joined (basedLocalizationFiberComparison P x) y :=
  (basedLocalizationFiberComparison_isWeakHomotopyEquivalence P).component_surjective y

example (s t : unitInterval) :
    (normalizedStructuredFiberComparisonHomotopy P
      (s, (abelianExactStructure P.FullSubcategory).kBasepoint)).1.2 t =
        (abelianExactStructure P.isoModSerre.Localization).kBasepoint := by
  rw [normalizedStructuredFiberComparisonHomotopy_based]
  rfl
