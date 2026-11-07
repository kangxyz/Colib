/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.PrespectrumHomotopy

/-! Actual identity and binary composition homotopies for canonically normalized exact-functor
spectrum maps. No strict functor or higher associativity coherence is asserted. -/
/-! Implementation provenance:
`Quillen/Waldhausen/SConstruction/Iterated/ExactCoherence.lean` at Quillen
commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, complete
based tracks, signed degrees, hypotheses and independent universes are retained.
The small source is the native `WideSubcategory preservesZero` on
`SmallWaldhausenCategory`, with the existing `AsSmall` transport. -/
@[expose] public section


noncomputable section
open Topology SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor
open scoped Topology unitInterval
universe u v
namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  (W : Structure C) (V : Structure D) (U : Structure E)

lemma asSmallCategoryMap_id :
    asSmallCategoryMap W W (IsExact.id _ _) rfl = 𝟙 (asSmallCategory W) := by
  apply WideSubcategory.hom_ext
  apply SmallWaldhausenCategory.Hom.ext
  rfl

lemma asSmallCategoryMap_comp {F : C ⥤ D} {G : D ⥤ E}
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (hG : IsExact V.cof V.weq U.cof U.weq G)
    (h0F : F.obj W.zero = V.zero) (h0G : G.obj V.zero = U.zero) :
    asSmallCategoryMap W U (hF.comp hG) ((congrArg G.obj h0F).trans h0G) =
      asSmallCategoryMap W V hF h0F ≫ asSmallCategoryMap V U hG h0G := by
  apply WideSubcategory.hom_ext
  apply SmallWaldhausenCategory.Hom.ext
  rfl

lemma originalPrespectrumMap_id :
    originalPrespectrumMap W W (IsExact.id _ _) rfl = 𝟙 (originalPrespectrum W) := by
  change prespectrumFunctor.map (asSmallCategoryMap W W (IsExact.id _ _) rfl) =
    𝟙 (prespectrumFunctor.obj (asSmallCategory W))
  rw [asSmallCategoryMap_id, CategoryTheory.Functor.map_id]

lemma originalPrespectrumMap_comp {F : C ⥤ D} {G : D ⥤ E}
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (hG : IsExact V.cof V.weq U.cof U.weq G)
    (h0F : F.obj W.zero = V.zero) (h0G : G.obj V.zero = U.zero) :
    originalPrespectrumMap W U (hF.comp hG) ((congrArg G.obj h0F).trans h0G) =
      originalPrespectrumMap W V hF h0F ≫ originalPrespectrumMap V U hG h0G := by
  change prespectrumFunctor.map (asSmallCategoryMap W U (hF.comp hG) _) = _
  rw [asSmallCategoryMap_comp W V U hF hG h0F h0G, CategoryTheory.Functor.map_comp]
  rfl

/-- The canonically normalized identity spectrum map has its actual coherent
homotopy to the literal identity map. -/
def exactOriginalPrespectrumMapIdHomotopy :
    LoopPrespectrum.Homotopy (exactOriginalPrespectrumMap W W (IsExact.id _ _))
      (𝟙 (originalPrespectrum W)) := by
  let h := IsExact.id W.cof W.weq
  let e := (CategoryTheory.rebaseFunctorIso (𝟭 C) W.zero W.zero
    ((h.zero W.isZero).iso W.isZero)).symm
  have H := originalPrespectrumTransformationHomotopy W W h.rebase h
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _) rfl e.hom (fun _A ↦ W.weq_iso _ inferInstance)
  simpa only [exactOriginalPrespectrumMap, originalPrespectrumMap_id] using H

/-- Composition holds by a genuine coherent spectrum homotopy induced by the
canonical normalization isomorphism, rather than by a false strict equality. -/
def exactOriginalPrespectrumMapCompHomotopy {F : C ⥤ D} {G : D ⥤ E}
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (hG : IsExact V.cof V.weq U.cof U.weq G) :
    LoopPrespectrum.Homotopy (exactOriginalPrespectrumMap W U (hF.comp hG))
      (exactOriginalPrespectrumMap W V hF ≫ exactOriginalPrespectrumMap V U hG) := by
  let iF := CategoryTheory.rebaseFunctorIso F W.zero V.zero ((hF.zero W.isZero).iso V.isZero)
  let iG := CategoryTheory.rebaseFunctorIso G V.zero U.zero ((hG.zero V.isZero).iso U.isZero)
  let iFG := CategoryTheory.rebaseFunctorIso (F ⋙ G) W.zero U.zero
    (((hF.comp hG).zero W.isZero).iso U.isZero)
  let e := iFG.symm ≪≫ isoWhiskerRight iF G ≪≫ isoWhiskerLeft _ iG
  have hf0 : (CategoryTheory.rebaseFunctor F W.zero V.zero ((hF.zero W.isZero).iso V.isZero)).obj
      W.zero = V.zero := CategoryTheory.rebaseFunctor_obj_base _ _ _ _
  have hg0 : (CategoryTheory.rebaseFunctor G V.zero U.zero ((hG.zero V.isZero).iso U.isZero)).obj
      V.zero = U.zero := CategoryTheory.rebaseFunctor_obj_base _ _ _ _
  have H := originalPrespectrumTransformationHomotopy W U (hF.comp hG).rebase
    (hF.rebase.comp hG.rebase) (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
    ((congrArg (CategoryTheory.rebaseFunctor G V.zero U.zero ((hG.zero V.isZero).iso U.isZero)).obj
      hf0).trans hg0)
    e.hom (fun _A ↦ U.weq_iso _ inferInstance)
  rw [originalPrespectrumMap_comp W V U hF.rebase hG.rebase hf0 hg0] at H
  exact H

end CategoryTheory.Waldhausen.IteratedS
