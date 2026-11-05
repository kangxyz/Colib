/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.CanonicalMap
public import Colib.KTheory.Waldhausen.HomotopyMap

/-! # Functoriality of canonical KMap for arbitrary exact functors

Adapted from Quillen/Waldhausen/Functoriality/KMap.lean at commit
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual normalized weak transformation
and its fixed-zero homotopy identify canonical K-maps; no arbitrary free homotopy
is silently treated as based. The model remains unnormalized IsZero-diagonal.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u v
namespace CategoryTheory.Waldhausen
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
variable {V : Structure C} {W : Structure D} {U : Structure E}
variable {F G : C ⥤ D}

/-- Conjugate the actual transformation by the two canonical zero normalizations. -/
def normalizedWeakTransformation
    (hF : IsExact V.cof V.weq W.cof W.weq F)
    (hG : IsExact V.cof V.weq W.cof W.weq G) (η : F ⟶ G) :
    CategoryTheory.rebaseFunctor F V.zero W.zero ((hF.zero V.isZero).iso W.isZero) ⟶
      CategoryTheory.rebaseFunctor G V.zero W.zero ((hG.zero V.isZero).iso W.isZero) :=
  (CategoryTheory.rebaseFunctorIso F V.zero W.zero ((hF.zero V.isZero).iso W.isZero)).inv ≫ η ≫
    (CategoryTheory.rebaseFunctorIso G V.zero W.zero ((hG.zero V.isZero).iso W.isZero)).hom

/-- Actual pointwise weakness survives this concrete conjugation. -/
theorem normalizedWeakTransformation_weak
    (hF : IsExact V.cof V.weq W.cof W.weq F)
    (hG : IsExact V.cof V.weq W.cof W.weq G) (η : F ⟶ G)
    (hη : ∀ X, W.weq (η.app X)) (X : C) :
    W.weq ((normalizedWeakTransformation hF hG η).app X) :=
  W.weq.comp_mem _ _ (W.weq_iso _ inferInstance)
    (W.weq.comp_mem _ _ (hη X) (W.weq_iso _ inferInstance))

/-- A pointwise weak natural transformation gives equality of the original
canonical chosen-zero K-homomorphisms in every degree. -/
theorem KMap_eq_of_weakNatTrans
    (hF : IsExact V.cof V.weq W.cof W.weq F)
    (hG : IsExact V.cof V.weq W.cof W.weq G) (η : F ⟶ G)
    (hη : ∀ X, W.weq (η.app X)) (n : ℕ) : KMap hF n = KMap hG n := by
  rw [KMap_eq_piMap hF n, KMap_eq_piMap hG n]
  exact HomotopyGroup.piMap_eq_of_based_homotopy n _ _
    (weakNaturalTransformationRealizationHomotopy V W hF.rebase hG.rebase
      (normalizedWeakTransformation hF hG η) (normalizedWeakTransformation_weak hF hG η hη))
    (weakNaturalTransformationRealizationHomotopy_fixed_zero V W hF.rebase hG.rebase
      (normalizedWeakTransformation hF hG η) (normalizedWeakTransformation_weak hF hG η hη)
      (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
      (CategoryTheory.rebaseFunctor_obj_base _ _ _ _))

/-- Natural isomorphisms preserve the original canonical K-map. -/
theorem KMap_eq_of_iso
    (hF : IsExact V.cof V.weq W.cof W.weq F)
    (hG : IsExact V.cof V.weq W.cof W.weq G) (e : F ≅ G) (n : ℕ) :
    KMap hF n = KMap hG n :=
  KMap_eq_of_weakNatTrans hF hG e.hom (fun _ ↦ W.weq_iso _ inferInstance) n

/-- The original S-map preserves composition exactly. -/
@[simp] theorem sSetMap_comp_sSetMap {J : D ⥤ E}
    (hF : IsExact V.cof V.weq W.cof W.weq F)
    (hJ : IsExact W.cof W.weq U.cof U.weq J) :
    sSetMap hF ≫ sSetMap hJ =
      sSetMap (hF.comp hJ) := by
  ext n A
  rfl


/-- Composition of the original realization maps is literal realization functoriality. -/
@[simp] theorem deloopingMap_comp_deloopingMap {J : D ⥤ E}
    (hF : IsExact V.cof V.weq W.cof W.weq F)
    (hJ : IsExact W.cof W.weq U.cof U.weq J) :
    deloopingMap hF ≫ deloopingMap hJ =
      deloopingMap (hF.comp hJ) := by
  simp only [deloopingMap, ← Functor.map_comp, sSetMap_comp_sSetMap]


private theorem piMap_congr {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (n : ℕ) {f g : C(X, Y)} (hf : f x = y) (hg : g x = y)
    (h : f = g) : HomotopyGroup.piMap n f hf = HomotopyGroup.piMap n g hg := by
  subst g
  rfl

/-- Composition of exact functors gives composition of the original canonical
chosen-zero K-homomorphisms. -/
@[simp] theorem KMap_comp_KMap {J : D ⥤ E}
    (hF : IsExact V.cof V.weq W.cof W.weq F)
    (hJ : IsExact W.cof W.weq U.cof U.weq J) (n : ℕ) :
    (KMap hJ n).comp (KMap hF n) =
      KMap (hF.comp hJ) n := by
  symm
  let eF := CategoryTheory.rebaseFunctorIso F V.zero W.zero ((hF.zero V.isZero).iso W.isZero)
  let eJ := CategoryTheory.rebaseFunctorIso J W.zero U.zero ((hJ.zero W.isZero).iso U.isZero)
  have h0 : ((CategoryTheory.rebaseFunctor F V.zero W.zero ((hF.zero V.isZero).iso W.isZero)) ⋙
      (CategoryTheory.rebaseFunctor J W.zero U.zero ((hJ.zero W.isZero).iso U.isZero))).obj V.zero =
          U.zero := by
    change (CategoryTheory.rebaseFunctor J W.zero U.zero ((hJ.zero W.isZero).iso U.isZero)).obj
      ((CategoryTheory.rebaseFunctor F V.zero W.zero
        ((hF.zero V.isZero).iso W.isZero)).obj V.zero) =
          U.zero
    rw [CategoryTheory.rebaseFunctor_obj_base, CategoryTheory.rebaseFunctor_obj_base]
  have he := KMap_eq_of_iso (hF.comp hJ) (hF.rebase.comp hJ.rebase)
    (Functor.isoWhiskerRight eF J ≪≫ Functor.isoWhiskerLeft _ eJ) n
  rw [he, KMap_eq_piMap_of_zeroEq _ h0 n, KMap_eq_piMap hF n, KMap_eq_piMap hJ n]
  exact (piMap_congr n
    (f := (deloopingMap (hF.rebase.comp hJ.rebase)).hom)
    (g := (deloopingMap hJ.rebase).hom.comp (deloopingMap hF.rebase).hom) _
    ((congrArg (deloopingMap hJ.rebase).hom (KMap_basepoint hF)).trans (KMap_basepoint hJ))
    (congrArg TopCat.Hom.hom ((deloopingMap_comp_deloopingMap hF.rebase hJ.rebase).symm))).trans
      (HomotopyGroup.mapHom_comp (N := Fin (n + 1))
        (deloopingMap hF.rebase).hom (KMap_basepoint hF)
        (deloopingMap hJ.rebase).hom (KMap_basepoint hJ))


end CategoryTheory.Waldhausen

attribute [colib_tag "COL-0158",
  colib_ref "Waldhausen1985" "Section 1.3, pp. 328-330" "background"
    "Exact functoriality background; canonical rebasing is explicit in the unnormalized model"]
  CategoryTheory.Waldhausen.KMap_eq_of_weakNatTrans
  CategoryTheory.Waldhausen.KMap_eq_of_iso
  CategoryTheory.Waldhausen.KMap_comp_KMap
