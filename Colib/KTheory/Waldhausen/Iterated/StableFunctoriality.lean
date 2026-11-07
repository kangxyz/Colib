/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Iterated.ExactCoherence
public import Colib.KTheory.Waldhausen.Iterated.StableHomotopy
public import Colib.Topology.Prespectrum.StableEquivalence

/-!
Original exact-functor stable maps, identity/composition laws, weak-natural-transformation
invariance, and naturality of every original nonnegative K-group comparison. Stable equivalence of
these connective spectrum maps is equivalent to bijectivity of every original K-map, including K0;
negative degrees use the proved connectivity.
-/
/-! Implementation provenance:
`Quillen/Waldhausen/SConstruction/Iterated/StableFunctoriality.lean` at Quillen
commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, complete
based tracks, signed degrees, hypotheses and independent universes are retained.
The small source is the native `WideSubcategory preservesZero` on
`SmallWaldhausenCategory`, with the existing `AsSmall` transport. -/
@[expose] public section


noncomputable section
open Topology SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology.LoopPrespectrum
universe u v
namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  (W : Structure C) (V : Structure D) (U : Structure E)
  {F G : C ⥤ D} (hF : IsExact W.cof W.weq V.cof V.weq F)
  (hG : IsExact W.cof W.weq V.cof V.weq G)

/-- The integer-graded stable homotopy map induced by the given exact functor. -/
def exactStableKMap (d : ℤ) :
    stableHomotopyGroup (originalPrespectrum W) d ⟶ stableHomotopyGroup (originalPrespectrum V) d :=
  (stableHomotopyFunctor d).map (exactOriginalPrespectrumMap W V hF)

lemma exactStableKMap_id (d : ℤ) :
    exactStableKMap W W (IsExact.id _ _) d = 𝟙 _ := by
  exact ((exactOriginalPrespectrumMapIdHomotopy W).stableHomotopyMap_eq d).trans
    ((stableHomotopyFunctor d).map_id _)

lemma exactStableKMap_comp {J : D ⥤ E} (hJ : IsExact V.cof V.weq U.cof U.weq J) (d : ℤ) :
    exactStableKMap W U (hF.comp hJ) d = exactStableKMap W V hF d ≫ exactStableKMap V U hJ d := by
  exact ((exactOriginalPrespectrumMapCompHomotopy W V U hF hJ).stableHomotopyMap_eq d).trans
    ((stableHomotopyFunctor d).map_comp _ _)

lemma exactStableKMap_weakNatTrans (η : F ⟶ G) (hη : ∀ A, V.weq (η.app A)) (d : ℤ) :
    exactStableKMap W V hF d = exactStableKMap W V hG d :=
  (exactOriginalPrespectrumHomotopy W V hF hG η hη).stableHomotopyMap_eq d

lemma exactStableKMap_iso (e : F ≅ G) (d : ℤ) :
    exactStableKMap W V hF d = exactStableKMap W V hG d :=
  (exactOriginalPrespectrumIsoHomotopy W V hF hG e).stableHomotopyMap_eq d

lemma originalKStableEquiv_exact_naturality (n : ℕ) (a : W.K n) :
    originalKStableEquiv V n (Additive.ofMul (KMap hF n a)) =
      exactStableKMap W V hF (n : ℤ) (originalKStableEquiv W n (Additive.ofMul a)) := by
  have h := KMap_eq_of_iso hF hF.rebase
    (CategoryTheory.rebaseFunctorIso F W.zero V.zero ((hF.zero W.isZero).iso V.isZero)) n
  rw [h]
  exact originalKStableEquiv_naturality W V hF.rebase
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _) n a

end CategoryTheory.Waldhausen.IteratedS

end


noncomputable section
open Topology SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology.LoopPrespectrum
universe u v
namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) (V : Structure D) {F : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F)

lemma exactStableKMap_nonnegative_bijective_iff (n : ℕ) :
    Function.Bijective (exactStableKMap W V hF (n : ℤ)) ↔ Function.Bijective (KMap hF n) := by
  let eW := originalKStableEquiv W n
  let eV := originalKStableEquiv V n
  have he : (fun a : Additive (W.K n) ↦ eV (Additive.ofMul (KMap hF n a.toMul))) =
      (exactStableKMap W V hF (n : ℤ)) ∘ eW := by
    funext a
    exact originalKStableEquiv_exact_naturality W V hF n a.toMul
  constructor
  · intro h
    have hc := h.comp eW.bijective
    rw [← he] at hc
    exact (eV.bijective.of_comp_iff' _).mp hc
  · intro h
    have hc : Function.Bijective (fun a : Additive (W.K n) ↦ eV (Additive.ofMul (KMap hF n
      a.toMul))) :=
      eV.bijective.comp h
    rw [he] at hc
    exact (Function.Bijective.of_comp_iff _ eW.bijective).mp hc

/-- Every original K-map is bijective exactly when its actual normalized connective
spectrum map is a stable equivalence. Negative degrees are derived from connectivity. -/
lemma exactOriginalPrespectrumMap_isStableEquivalence_iff :
    IsStableEquivalence (exactOriginalPrespectrumMap W V hF) ↔
      ∀ n : ℕ, Function.Bijective (KMap hF n) := by
  constructor
  · intro h n
    apply (exactStableKMap_nonnegative_bijective_iff W V hF n).mp
    exact (ConcreteCategory.isIso_iff_bijective _).mp (h n)
  · intro h d
    change IsIso (exactStableKMap W V hF d)
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    by_cases hd : d < 0
    · let := originalStableHomotopyGroup_neg_subsingleton W d hd
      let := originalStableHomotopyGroup_neg_subsingleton V d hd
      exact Function.bijective_of_subsingleton' _
    · have he : d = (d.toNat : ℤ) := by omega
      rw [he]
      exact (exactStableKMap_nonnegative_bijective_iff W V hF d.toNat).mpr (h d.toNat)

end CategoryTheory.Waldhausen.IteratedS

attribute [colib_tag "COL-0283"]
  CategoryTheory.Waldhausen.IteratedS.originalKStableEquiv_exact_naturality
  CategoryTheory.Waldhausen.IteratedS.exactOriginalPrespectrumMap_isStableEquivalence_iff
