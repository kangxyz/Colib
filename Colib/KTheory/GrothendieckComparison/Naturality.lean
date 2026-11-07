/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.GrothendieckComparison.ObjectLoops
public import Colib.KTheory.GrothendieckGroup.Map
public import Colib.KTheory.GrothendieckGroup.Multiplicative
public import Colib.KTheory.Quillen.Map.Basic
public import Colib.CategoryTheory.QConstruction.ObjectClassRebase
public import Colib.CategoryTheory.ExactCategory.Functor.ObjectClass
public import Colib.Topology.ClassifyingSpace.ArrowPathsNaturality
public import Colib.Topology.Homotopy.HomotopyGroup.FundamentalGroup

/-!
# Naturality of the canonical Grothendieck–Quillen comparison

Adapted from `Quillen/KTheory/GrothendieckComparison/Naturality.lean` at
Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original maps, specified basepoint equalities and multiplication order are retained.
-/

@[expose] public noncomputable section

universe u v
open CategoryTheory CategoryTheory.Limits
open scoped Topology ZeroObject
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.ExactCategory.ExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- Realization sends the canonical object-loop class through the functor
on Q, with precisely the chosen equality of target basepoints. -/
lemma fundamentalMap_qObjectClass {D : Type u} [Category.{max u v} D]
    (F : E.QCategory ⥤ D) (d : D) (h : F.obj E.qZero = d) (X : C) :
    FundamentalGroup.mapOfEq (X := ClassifyingSpace E.QCategory) (Y := ClassifyingSpace D)
        (x := classifyingSpacePoint E.qZero) (y := classifyingSpacePoint d) (classifyingSpaceMap
          F).hom
        ((classifyingSpaceMap_point F E.qZero).trans (congrArg classifyingSpacePoint h))
        (E.qObjectClass (classifyingFundamentalGroupoidFunctor E.QCategory) X) =
      ((classifyingFundamentalGroupoidFunctor D).mapIso (eqToIso h)).conj
        (E.qObjectClass (F ⋙ classifyingFundamentalGroupoidFunctor D) X) := by
  subst d
  rw [E.qObjectClass_natIso (classifyingFundamentalGroupoidNaturality F) X]
  erw [← Iso.trans_conj, E.qObjectClass_comp]
  apply congrArg₂ (fun (e : FundamentalGroupoid.mk
      ((classifyingSpaceMap F).hom (classifyingSpacePoint E.qZero)) ≅
        FundamentalGroupoid.mk (classifyingSpacePoint (F.obj E.qZero)))
      (a : End (FundamentalGroupoid.mk ((classifyingSpaceMap F).hom (classifyingSpacePoint
        E.qZero)))) => e.conj a)
  · apply Iso.ext
    dsimp [classifyingFundamentalGroupoidNaturality, classifyingFundamentalGroupoidFunctor,
      eqToIso]
    simp only [classifyingSpacePath_id, Path.Homotopic.Quotient.mk_refl]
    change eqToHom _ = eqToHom _ ≫ 𝟙 _
    simp
  · rfl

end CategoryTheory.ExactCategory.ExactStructure

namespace CategoryTheory.ExactCategory.ExactFunctor

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [HasFiniteBiproducts C] [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D}

/-- The exact-functor K-map carries every canonical object loop to the loop
of its image object. This uses the same zero normalization as `KMap`. -/
@[simp] theorem KMap_kZeroObjectClass (F : ExactFunctor EC ED) (X : C) :
    F.KMap 0 (EC.kZeroObjectClass X) = ED.kZeroObjectClass (F.toFunctor.obj X) := by
  let e := ED.qIsoOfIso F.toFunctor.mapZeroObject
  let G := rebaseFunctor F.mapQ EC.qZero ED.qZero e
  have hG : G.obj EC.qZero = ED.qZero := rebaseFunctor_obj_base F.mapQ EC.qZero ED.qZero e
  apply ED.kZeroFundamentalGroupEquiv.injective
  change HomotopyGroup.pi1MulEquivFundamentalGroup
    (HomotopyGroup.map (classifyingSpaceMap G).hom
      ((classifyingSpaceMap_point G EC.qZero).trans (congrArg classifyingSpacePoint hG))
      (EC.kZeroObjectClass X)) = _
  rw [HomotopyGroup.pi1MulEquivFundamentalGroup_naturality]
  change FundamentalGroup.mapOfEq _ _
    (EC.kZeroFundamentalGroupEquiv (EC.kZeroObjectClass X)) = _
  rw [EC.kZeroFundamentalGroupEquiv_objectClass, ED.kZeroFundamentalGroupEquiv_objectClass,
    EC.kZeroObjectLoop_eq_qObjectClass, ED.kZeroObjectLoop_eq_qObjectClass]
  erw [EC.fundamentalMap_qObjectClass G ED.qZero hG X,
    EC.rebase_qObjectClass F.mapQ ED.qZero e _ X]
  exact F.qObjectClass_mapQ _ X

/-- The algebraic-to-homotopical K₀ comparison is natural for every exact
functor, with the canonical maps already used elsewhere in the project. -/
theorem grothendieckToKZero_naturality (F : ExactFunctor EC ED) :
    (F.KMap 0).comp EC.grothendieckToKZero =
      ED.grothendieckToKZero.comp F.grothendieckMap.toMultiplicative := by
  apply EC.grothendieck_mulHom_ext
  intro X
  simp

end CategoryTheory.ExactCategory.ExactFunctor

attribute [colib_ref "WeibelKBook"
  "IV, Proposition 6.2 and proof, equations (6.2.1)-(6.2.2), page 54" "adaptation"
  "Naturality of the original object-loop comparison under the zero-normalized exact-functor map"]
  CategoryTheory.ExactCategory.ExactFunctor.KMap_kZeroObjectClass
  CategoryTheory.ExactCategory.ExactFunctor.grothendieckToKZero_naturality
