/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.CanonicalMap

public import Colib.CategoryTheory.Waldhausen.Additivity.NormalizedDeformationMap
public import Colib.CategoryTheory.Waldhausen.Additivity.NormalizedSumMap
public import Colib.CategoryTheory.Waldhausen.Additivity.EndpointFamilies

/-! # Genuine coherent endpoint families after chosen-zero normalization

The families are actual conjugates of the already proved endpoint natural
isomorphisms. Their weakness and independent reindexing coherence are proved
from those concrete isomorphisms; no homotopy or basedness conclusion is assumed.


Implementation provenance: `Quillen/Waldhausen/Additivity/NormalizedEndpointFamilies.lean`
at commit c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps, hypotheses and
universes are retained; no subdivision realization equivalence is assumed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
universe u v

namespace CategoryTheory.Waldhausen.Additivity

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (V : Structure C) (W : Structure D) {F G H : C ⥤ D} (a : F ⟶ G)
variable (hF : IsExact V.cof V.weq W.cof W.weq F)
variable (hG : IsExact V.cof V.weq W.cof W.weq G)
variable (hc : IsCofibrationTransformation W a V)

/-- The identity endpoint's actual natural iso to the canonical rebased middle functor. -/
def normalizedIdentityEndpointIso (n m : SimplexCategoryᵒᵖ)
    (A : ((bisimplicialSSet V).obj n).obj m) :
    (((normalizedIdentityMap V W a hF hG hc).app n).app m A).1 ≅
      (((bisimplicialSSetMap V.cof V.weq hG.rebase).app n).app m A).1 :=
  (Functor.isoWhiskerLeft (intervalArrows (𝟙 n.unop) (𝟙 n.unop) (fun _ ↦ le_rfl) A.1)
    (normalizedPushoutIso V W a hF hG hc).symm) ≪≫
    identityDeformationIso V W a hc (𝟙 n.unop) A.1 ≪≫
    Functor.isoWhiskerLeft A.1
      (CategoryTheory.rebaseFunctorIso G V.zero W.zero ((hG.zero V.isZero).iso W.isZero))

/-- The normalized identity endpoint family retains the actual normalization maps. -/
def normalizedIdentityEndpointFamily (n m : SimplexCategoryᵒᵖ)
    (A : ((bisimplicialSSet V).obj n).obj m) :
    (((normalizedIdentityMap V W a hF hG hc).app n).app m A).1 ⟶
      (((bisimplicialSSetMap V.cof V.weq hG.rebase).app n).app m A).1 :=
  (normalizedIdentityEndpointIso V W a hF hG hc n m A).hom

/-- Every actual component is an isomorphism and therefore weak. -/
theorem normalizedIdentityEndpointFamily_weak (n m : SimplexCategoryᵒᵖ)
    (A : ((bisimplicialSSet V).obj n).obj m) (x : Grid₂ n.unop m.unop) :
    W.weq ((normalizedIdentityEndpointFamily V W a hF hG hc n m A).app x) :=
  W.weq_iso _ (by
    change IsIso ((normalizedIdentityEndpointIso V W a hF hG hc n m A).hom.app x)
    infer_instance)

/-- Actual component coherence under independent interval and nerve restriction. -/
theorem normalizedIdentityEndpointFamily_reindex_app {n n' m m' : SimplexCategory}
    (α : n' ⟶ n) (β : m' ⟶ m)
    (A : ((bisimplicialSSet V).obj (op n)).obj (op m)) (x : Grid₂ n' m') :
    HEq ((normalizedIdentityEndpointFamily V W a hF hG hc (op n) (op m) A).app
      ((gridMap₂ α β).obj x))
      ((normalizedIdentityEndpointFamily V W a hF hG hc (op n') (op m')
        ⟨gridMap₂ α β ⋙ A.1, A.2.precomp V.cof V.weq α β⟩).app x) := by
  apply heq_of_eq
  simp only [normalizedIdentityEndpointFamily, normalizedIdentityEndpointIso, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom]
  exact congrArg (fun t ↦
    (normalizedPushoutIso V W a hF hG hc).inv.app
      ((intervalArrows (𝟙 n) (𝟙 n) (fun _ ↦ le_rfl) A.1).obj ((gridMap₂ α β).obj x)) ≫
      t ≫ (CategoryTheory.rebaseFunctorIso G V.zero W.zero ((hG.zero V.isZero).iso
        W.isZero)).hom.app
        (A.1.obj ((gridMap₂ α β).obj x)))
    (eq_of_heq (identityEndpointFamily_reindex_app V W a hF hG hc α β A x))

variable [HasBinaryCoproducts D]
variable (b : G ⟶ H) (hs : IsCofibrationSequence V W a b)

/-- The separated endpoint's actual natural iso to the common normalized pair-sum. -/
def normalizedSeparatedEndpointIso (n m : SimplexCategoryᵒᵖ)
    (A : ((SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V).obj n).obj m) :
    (((normalizedSeparatedMap V W a hs.exactF hs.exactG hs.cofibration).app n).app m A).1 ≅
      (((normalizedSumMap V W hs.exactH hs.exactF).app n).app m A).1 :=
  (Functor.isoWhiskerLeft
    (intervalArrows (SSet.OrdinalJoin.left n.unop n.unop) (SSet.OrdinalJoin.right n.unop n.unop)
      (left_le_right n.unop) A.1)
    (normalizedPushoutIso V W a hs.exactF hs.exactG hs.cofibration).symm) ≪≫
    separatedDeformationIso V W a (SSet.OrdinalJoin.left n.unop n.unop)
      (SSet.OrdinalJoin.right n.unop n.unop)
      (left_le_right n.unop) (left_separated_right n.unop) b hs A.2 ≪≫
    Functor.isoWhiskerLeft (separatedPairGrid A.1) (normalizedSplitIso V W hs.exactH hs.exactF)

/-- The actual separated family is the conjugate of the original cofiber comparison. -/
def normalizedSeparatedEndpointFamily (n m : SimplexCategoryᵒᵖ)
    (A : ((SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V).obj n).obj m) :
    (((normalizedSeparatedMap V W a hs.exactF hs.exactG hs.cofibration).app n).app m A).1 ⟶
      (((normalizedSumMap V W hs.exactH hs.exactF).app n).app m A).1 :=
  (normalizedSeparatedEndpointIso V W a b hs n m A).hom

/-- These concrete conjugate components are isomorphisms and hence weak. -/
theorem normalizedSeparatedEndpointFamily_weak (n m : SimplexCategoryᵒᵖ)
    (A : ((SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V).obj n).obj m)
    (x : Grid₂ n.unop m.unop) :
    W.weq ((normalizedSeparatedEndpointFamily V W a b hs n m A).app x) :=
  W.weq_iso _ (by
    change IsIso ((normalizedSeparatedEndpointIso V W a b hs n m A).hom.app x)
    infer_instance)

private theorem normalizedCofiberEndpointIso_hom_heq {f g : Arrow C} (hfg : f = g)
    (hf : F.map f.hom = zeroMorphism W (F.obj f.left) (F.obj f.right))
    (hg : F.map g.hom = zeroMorphism W (F.obj g.left) (F.obj g.right)) :
    HEq (((normalizedPushoutIso V W a hs.exactF hs.exactG hs.cofibration).app f).symm ≪≫
        cofiberEndpointIso W a hs.cofibration.app_cof f (b.app f.left) (hs.cofiber f.left) hf ≪≫
        (normalizedSplitIso V W hs.exactH hs.exactF).app (f.left, f.right)).hom
      (((normalizedPushoutIso V W a hs.exactF hs.exactG hs.cofibration).app g).symm ≪≫
        cofiberEndpointIso W a hs.cofibration.app_cof g (b.app g.left) (hs.cofiber g.left) hg ≪≫
        (normalizedSplitIso V W hs.exactH hs.exactF).app (g.left, g.right)).hom := by
  subst g
  rfl

/-- The separated conjugate family is strictly coherent on actual components
under simultaneous independent reindexing. -/
theorem normalizedSeparatedEndpointFamily_reindex_app {n n' m m' : SimplexCategory}
    (α : n' ⟶ n) (β : m' ⟶ m)
    (A : ((SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V).obj (op n)).obj (op m))
    (x : Grid₂ n' m') :
    HEq ((normalizedSeparatedEndpointFamily V W a b hs (op n) (op m) A).app
      ((gridMap₂ α β).obj x))
      ((normalizedSeparatedEndpointFamily V W a b hs (op n') (op m')
        ⟨gridMap₂ (SSet.OrdinalSubdivision.δ.map α) β ⋙ A.1,
          A.2.precomp V.cof V.weq (SSet.OrdinalSubdivision.δ.map α) β⟩).app x) := by
  refine normalizedCofiberEndpointIso_hom_heq V W a b hs
    (congrArg (fun T ↦ T.obj x) (separatedIntervalArrows_reindex α β A.1)) ?_ ?_
  · exact (congrArg F.map (intervalArrows_separated_hom V (SSet.OrdinalJoin.left n n)
      (SSet.OrdinalJoin.right n n) (left_le_right n) (left_separated_right n) A.2
      ((gridMap₂ α β).obj x))).trans (map_zeroMorphism V W hs.exactF _ _)
  · exact (congrArg F.map (intervalArrows_separated_hom V (SSet.OrdinalJoin.left n' n')
      (SSet.OrdinalJoin.right n' n') (left_le_right n') (left_separated_right n')
      (A.2.precomp V.cof V.weq (SSet.OrdinalSubdivision.δ.map α) β) x)).trans
      (map_zeroMorphism V W hs.exactF _ _)

end CategoryTheory.Waldhausen.Additivity
