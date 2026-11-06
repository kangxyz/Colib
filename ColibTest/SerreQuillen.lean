module

import Colib.KTheory.Quillen.Localization.Serre.KZero
import Colib.KTheory.Quillen.Localization.Serre.FiberBoundary

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.ExactCategory.SerreLocalization Topology

universe u v

attribute [local instance] Abelian.hasFiniteBiproducts

section Naturality

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [HasFiniteBiproducts C] [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D} (F : ExactFunctor EC ED)

example (X : C) :
    F.KMap 0 (EC.kZeroObjectClass X) = ED.kZeroObjectClass (F.toFunctor.obj X) :=
  F.KMap_kZeroObjectClass X

example : (F.KMap 0).comp EC.grothendieckToKZero =
    ED.grothendieckToKZero.comp F.grothendieckMap.toMultiplicative :=
  F.grothendieckToKZero_naturality

example (a : Multiplicative EC.GrothendieckGroup) :
    F.KMap 0 (EC.grothendieckKZeroEquiv a) =
      ED.grothendieckKZeroEquiv (F.grothendieckMap.toMultiplicative a) :=
  DFunLike.congr_fun F.grothendieckToKZero_naturality a

end Naturality

section GeneralLocalization

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Abelian C] [Abelian D] (P : ObjectProperty C) [P.IsSerreClass]
  (L : C ⥤ D) [L.IsLocalization P.isoModSerre] [L.Additive]

example : (Abelian.Devissage.grothendieckMap P).range = serreSubgroup P :=
  inclusionGrothendieckMap_range P

example : Function.Surjective (SerreLocalization.KMap P L 0) :=
  KZeroMap_surjective P L

example : (Abelian.Devissage.KMap P 0).range = (SerreLocalization.KMap P L 0).ker :=
  inclusionKZero_range_eq_ker P L

end GeneralLocalization

section CanonicalQuotient

attribute [local instance] canonicalQuotientAbelian

variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

example : Function.Surjective (quotientKMap P 0) := quotientKZero_surjective P

example : (Abelian.Devissage.KMap P 0).range = (quotientKMap P 0).ker :=
  inclusion_range_eq_quotientKZero_ker P

example : basedLocalizationFiberComparison P
    (abelianExactStructure P.FullSubcategory).kBasepoint = normalizedFiberBasepoint P :=
  basedLocalizationFiberComparison_basepoint P

example (n : ℕ) :
    (localizationFiberProjectionHom P n).comp (localizationFiberComparisonHom P n) =
      Abelian.Devissage.KMap P n := localizationFiberComparisonHom_projection P n

example (n : ℕ) :
    (quotientKMap P n).comp (Abelian.Devissage.KMap P n) = 1 :=
  quotientKMap_comp_inclusion P n

example (n : ℕ) :
    (quotientKMap P (n + 1)).range = (fiberConnectingHom P n).ker :=
  quotient_range_eq_fiberConnecting_ker P n

example (n : ℕ) :
    (fiberConnectingHom P n).range = (localizationFiberProjectionHom P n).ker :=
  fiberConnecting_range_eq_projection_ker P n

example (n : ℕ) :
    (localizationFiberProjectionHom P n).range = (quotientKMap P n).ker :=
  fiberProjection_range_eq_quotient_ker P n

example (n : ℕ) : (Abelian.Devissage.KMap P n).range ≤ (quotientKMap P n).ker :=
  inclusion_range_le_quotient_ker P n

end CanonicalQuotient
