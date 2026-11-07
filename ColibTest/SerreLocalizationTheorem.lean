/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Quillen.Localization.Serre.LocalizationTheorem

/-!
# Canonical connective Serre localization regression clients

The only category assumptions are the original small abelian category and
Serre class. No comparison, filtration or exactness witness is supplied.
-/

@[expose] public noncomputable section

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.ExactCategory.SerreLocalization Topology
attribute [local instance] Abelian.hasFiniteBiproducts canonicalQuotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

example : IsWeakHomotopyEquivalence (basedLocalizationFiberComparison P) :=
  basedLocalizationFiberComparison_isWeakHomotopyEquivalence P

example : Function.Bijective (HomotopyGroup.map (N := Fin 0)
    (basedLocalizationFiberComparison P) (basedLocalizationFiberComparison_basepoint P)) :=
  basedLocalizationFiberComparison_bijective P 0

example (n : ℕ) : (localizationFiberEquiv P n).toMonoidHom =
    localizationFiberComparisonHom P n := rfl

example (n : ℕ) : connectingHom P n =
    (localizationFiberEquiv P n).symm.toMonoidHom.comp (fiberConnectingHom P n) := rfl

example (n : ℕ) :
    (localizationFiberComparisonHom P n).comp (connectingHom P n) =
      fiberConnectingHom P n := comparison_comp_connectingHom P n

example : (localizationFiberComparisonHom P 0).comp (connectingHom P 0) =
    fiberConnectingHom P 0 := comparison_comp_connectingHom P 0

example : (abelianExactStructure P.isoModSerre.Localization).K 1 →*
    (abelianExactStructure P.FullSubcategory).K 0 := connectingHom P 0

example (n : ℕ) :
    (Abelian.Devissage.KMap P n).range = (quotientKMap P n).ker :=
  inclusion_range_eq_quotient_ker P n

example (n : ℕ) :
    (quotientKMap P (n + 1)).range = (connectingHom P n).ker :=
  quotient_range_eq_connecting_ker P n

example (n : ℕ) :
    (connectingHom P n).range = (Abelian.Devissage.KMap P n).ker :=
  connecting_range_eq_inclusion_ker P n

example : KLocalizationSequence P := localizationSequence P

example (n : ℕ) : (localizationSequence P).connecting n = connectingHom P n := rfl

example :
    (∀ n, (Abelian.Devissage.KMap P n).range = (quotientKMap P n).ker) ∧
    (∀ n, (quotientKMap P (n + 1)).range = (connectingHom P n).ker) ∧
    (∀ n, (connectingHom P n).range = (Abelian.Devissage.KMap P n).ker) ∧
    Function.Surjective (quotientKMap P 0) := localization_longExact P

example :
    (quotientKMap P 1).range = (connectingHom P 0).ker ∧
    (connectingHom P 0).range = (Abelian.Devissage.KMap P 0).ker ∧
    (Abelian.Devissage.KMap P 0).range = (quotientKMap P 0).ker ∧
    Function.Surjective (quotientKMap P 0) := localization_KZero_tail P

example (n : ℕ)
    (δ : (abelianExactStructure P.isoModSerre.Localization).K (n + 1) →*
      (abelianExactStructure P.FullSubcategory).K n)
    (hδ : (localizationFiberComparisonHom P n).comp δ = fiberConnectingHom P n) :
    δ = connectingHom P n := connecting_unique P n δ hδ
