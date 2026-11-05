/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.WeakNaturalTransformationBased
public import Colib.Topology.Homotopy.HomotopyGroup.BasedHomotopy

/-! # Equality of exact-functor maps under explicit basedness

The original image-zero maps are compared only after the stated equalities
identify their targets with the same chosen zero. A general weak transformation
without these equalities gives a free homotopy, not this based conclusion.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe v u
namespace CategoryTheory.Waldhausen

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) {F G : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact V.cof V.weq W.cof W.weq G)
  (η : F ⟶ G) (hη : ∀ X, W.weq (η.app X))

/-- The equality-based target change is the usual homotopy-group map with
its transported basepoint proof; it introduces no extra path choice. -/
theorem groupsMapOfZeroEq_eq_piMap
    (Z : C) (hZ : IsZero Z) (Z' : D) (hZ' : IsZero Z')
    (h : F.obj Z = Z') (n : ℕ)
    (hb : (deloopingMap hF).hom (basepoint V.cof V.weq Z hZ) =
      basepoint W.cof W.weq Z' hZ') :
    groupsMapOfZeroEq hF Z hZ Z' hZ' h n =
      HomotopyGroup.piMap n (deloopingMap hF).hom hb := by
  subst Z'
  rfl

include η hη in
/-- Weak natural transformations identify the actual K-group maps when the two
image-zero objects are explicitly identified with the target's chosen zero. -/
theorem groupsMapOfZeroEq_eq_of_weakNaturalTransformation
    (hF0 : F.obj V.zero = W.zero) (hG0 : G.obj V.zero = W.zero) (n : ℕ) :
    groupsMapOfZeroEq hF V.zero V.isZero W.zero W.isZero hF0 n =
      groupsMapOfZeroEq hG V.zero V.isZero W.zero W.isZero hG0 n := by
  have hf : (deloopingMap hF).hom V.kBasepoint = W.kBasepoint := by
    simpa only [hF0] using deloopingMap_basepoint hF V.zero V.isZero
  have hg : (deloopingMap hG).hom V.kBasepoint = W.kBasepoint := by
    simpa only [hG0] using deloopingMap_basepoint hG V.zero V.isZero
  have he := HomotopyGroup.piMap_eq_of_based_homotopy n hf hg
    (weakNaturalTransformationRealizationHomotopy V W hF hG η hη)
    (weakNaturalTransformationRealizationHomotopy_fixed_zero V W hF hG η hη hF0 hG0)
  rw [groupsMapOfZeroEq_eq_piMap V W hF V.zero V.isZero W.zero W.isZero hF0 n hf,
    groupsMapOfZeroEq_eq_piMap V W hG V.zero V.isZero W.zero W.isZero hG0 n hg]
  exact he

end CategoryTheory.Waldhausen

attribute [colib_tag "COL-0157",
  colib_ref "Waldhausen1985" "Section 1.3, pp. 328-330" "background"
    "Background for the stated unnormalized IsZero model; not a strict-model identification"]
  CategoryTheory.Waldhausen.groupsMapOfZeroEq_eq_of_weakNaturalTransformation
