/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Map
public import Colib.CategoryTheory.Waldhausen.ExactFunctorIso
public import Colib.CategoryTheory.Functor.Rebase

/-!
# Canonical chosen-zero maps for the unnormalized Waldhausen model

Implementation provenance: PointedFunctor.lean and Functoriality/KMap.lean under
Quillen/Waldhausen at commit c561118b7795eb9780be9ed391c3251d6a4d0afd.
The actual rebased functor and based realization map are retained. The final
strict-zero reduction proof uses uniqueness of zero-object isomorphisms directly.
No strict-model comparison or additivity statement is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe v u
namespace CategoryTheory.Waldhausen
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : Structure C} {W' : Structure D}

/-- Exactness of the canonically rebased functor. -/
theorem IsExact.rebase {F : C ⥤ D} (hF : IsExact W.cof W.weq W'.cof W'.weq F) :
    IsExact W.cof W.weq W'.cof W'.weq
      (CategoryTheory.rebaseFunctor F W.zero W'.zero ((hF.zero W.isZero).iso W'.isZero)) :=
  hF.of_iso (CategoryTheory.rebaseFunctorIso F W.zero W'.zero ((hF.zero W.isZero).iso W'.isZero))

/-- The K-homomorphism induced by an exact functor, at the specified zero
objects of the two Waldhausen structures. -/
def KMap {F : C ⥤ D} (hF : IsExact W.cof W.weq W'.cof W'.weq F) (n : ℕ) :
    W.K n →* W'.K n :=
  groupsMapOfZeroEq hF.rebase W.zero W.isZero W'.zero W'.isZero
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _) n


variable {V : Structure C} {W : Structure D} {F : C ⥤ D}

/-- A strict chosen-zero equality makes the original realization map based. -/
theorem deloopingMap_basepoint_of_zeroEq
    (hF : IsExact V.cof V.weq W.cof W.weq F) (h0 : F.obj V.zero = W.zero) :
    deloopingMap hF V.kBasepoint = W.kBasepoint := by
  have h := deloopingMap_basepoint hF V.zero V.isZero
  simpa only [h0] using h

/-- The original canonical rebasing preserves the specified realization points. -/
theorem KMap_basepoint (hF : IsExact V.cof V.weq W.cof W.weq F) :
    deloopingMap hF.rebase V.kBasepoint = W.kBasepoint :=
  deloopingMap_basepoint_of_zeroEq hF.rebase (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)

private theorem groupsMapOfZeroEq_eq_piMap
    (hF : IsExact V.cof V.weq W.cof W.weq F)
    (Z : C) (hZ : IsZero Z) (Z' : D) (hZ' : IsZero Z') (h0 : F.obj Z = Z') (n : ℕ)
    (hb : deloopingMap hF (basepoint V.cof V.weq Z hZ) = basepoint W.cof W.weq Z' hZ') :
    groupsMapOfZeroEq hF Z hZ Z' hZ' h0 n = HomotopyGroup.piMap n (deloopingMap hF).hom hb := by
  subst Z'
  rfl

/-- The public K-map is exactly the based map of its original canonical rebasing. -/
theorem KMap_eq_piMap (hF : IsExact V.cof V.weq W.cof W.weq F) (n : ℕ) :
    KMap hF n = HomotopyGroup.piMap n (deloopingMap hF.rebase).hom (KMap_basepoint hF) :=
  groupsMapOfZeroEq_eq_piMap hF.rebase V.zero V.isZero W.zero W.isZero
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _) n (KMap_basepoint hF)


/-- Rebasing at an already equal zero leaves the underlying functor unchanged. -/
theorem rebaseFunctor_eq_of_zeroEq
    (hF : IsExact V.cof V.weq W.cof W.weq F) (h0 : F.obj V.zero = W.zero) :
    rebaseFunctor F V.zero W.zero ((hF.zero V.isZero).iso W.isZero) = F := by
  have he : (hF.zero V.isZero).iso W.isZero = eqToIso h0 := by
    apply Iso.ext
    exact (hF.zero V.isZero).eq_of_src _ _
  rw [he]
  have h : ∀ (d : D) (hd : F.obj V.zero = d),
      rebaseFunctor F V.zero d (eqToIso hd) = F := by
    intro d hd
    subst d
    exact rebaseFunctor_refl F V.zero
  exact h W.zero h0

/-- For an already based functor, canonical KMap is its original realization map. -/
theorem KMap_eq_piMap_of_zeroEq
    (hF : IsExact V.cof V.weq W.cof W.weq F) (h0 : F.obj V.zero = W.zero) (n : ℕ) :
    KMap hF n = HomotopyGroup.piMap n (deloopingMap hF).hom
      (deloopingMap_basepoint_of_zeroEq hF h0) := by
  rw [KMap_eq_piMap]
  congr 1
  have he := rebaseFunctor_eq_of_zeroEq hF h0
  unfold deloopingMap sSetMap
  congr 2
  simp only [he]

/-- Identity on the actual original realization. -/
@[simp] theorem deloopingMap_id (V : Structure C) :
    deloopingMap (IsExact.id V.cof V.weq) = 𝟙 V.Delooping := by
  rw [deloopingMap, sSetMap_id]
  exact SSet.toTop.map_id _

/-- The canonical KMap preserves identity without a homotopy-invariance assumption. -/
@[simp] theorem KMap_id (V : Structure C) (n : ℕ) :
    KMap (IsExact.id V.cof V.weq) n = MonoidHom.id (V.K n) := by
  rw [KMap_eq_piMap_of_zeroEq (IsExact.id V.cof V.weq) rfl n]
  have he : (deloopingMap (IsExact.id V.cof V.weq)).hom = ContinuousMap.id _ :=
    congrArg TopCat.Hom.hom (deloopingMap_id V)
  simp only [he]
  exact HomotopyGroup.mapHom_id

end CategoryTheory.Waldhausen

attribute [colib_tag "COL-0158",
  colib_ref "Waldhausen1985" "Section 1.3, pp. 328-330" "background"
    "Exact functoriality background; canonical rebasing is explicit in the unnormalized model"]
  CategoryTheory.Waldhausen.KMap
  CategoryTheory.Waldhausen.KMap_id
