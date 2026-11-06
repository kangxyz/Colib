/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Quillen.Map.NaturalIso
public import Colib.CategoryTheory.ExactCategory.Functor.ZeroNormalization

/-! # Zero normalization of the actual Quillen K-map

Adapted from `Quillen/Waldhausen/QuillenComparison/ZeroNormalization.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original functors,
canonical zero isomorphisms and based homotopies.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
universe v u v₁ v₂ u₁ u₂

namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

/-- The original equality isomorphism induces precisely equality transport in Q. -/
theorem qIsoOfIso_eqToIso_of_eq (E : ExactStructure C) {X Y : C} (h : X = Y) :
    E.qIsoOfIso (eqToIso h) = eqToIso (congrArg (QConstruction.of E.deflation E.inflation) h) := by
  subst Y
  exact E.qIsoOfIso_refl X
end CategoryTheory.ExactCategory.ExactStructure

namespace CategoryTheory.ExactCategory.ExactFunctor
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D} (F : ExactFunctor EC ED)

/-- Based natural-isomorphism invariance identifies its actual Quillen K-map. -/
theorem zeroNormalized_KMap (n : ℕ) : F.zeroNormalized.KMap n = F.KMap n :=
  (KMap_eq_of_natIso F.zeroNormalizedIso n).symm

/-- With strict zero preservation, the canonical zero isomorphism is equality transport. -/
theorem mapZeroObject_eq_eqToIso (h : F.toFunctor.obj (0 : C) = (0 : D)) :
    F.toFunctor.mapZeroObject = eqToIso h := by
  apply Iso.ext
  apply Subsingleton.elim

/-- No Q-rebasing is needed when the original functor already preserves zero strictly. -/
theorem normalizedQ_eq_mapQ_of_zeroEq (h : F.toFunctor.obj (0 : C) = (0 : D)) :
    F.normalizedQ = F.mapQ := by
  apply rebaseFunctor_eq_of_eq F.mapQ
    (QConstruction.of EC.deflation EC.inflation (0 : C))
    (QConstruction.of ED.deflation ED.inflation (0 : D)) _
    (congrArg (QConstruction.of ED.deflation ED.inflation) h)
  rw [mapZeroObject_eq_eqToIso F h,
    CategoryTheory.ExactCategory.ExactStructure.qIsoOfIso_eqToIso_of_eq]

/-- The unmodified Q-map is based when the functor strictly preserves zero. -/
theorem mapQ_map_point_of_zeroEq (h : F.toFunctor.obj (0 : C) = (0 : D)) :
    classifyingSpaceMap F.mapQ EC.kBasepoint = ED.kBasepoint := by
  rw [show EC.kBasepoint =
      classifyingSpacePoint (QConstruction.of EC.deflation EC.inflation (0 : C)) from rfl,
    classifyingSpaceMap_point]
  exact congrArg (fun X ↦ classifyingSpacePoint (QConstruction.of ED.deflation ED.inflation X)) h

/-- The actual normalized Quillen K-map agrees with the raw based map in this case. -/
theorem KMap_eq_piMap_of_zeroEq (h : F.toFunctor.obj (0 : C) = (0 : D)) (n : ℕ) :
    F.KMap n = HomotopyGroup.piMap n (classifyingSpaceMap F.mapQ).hom
      (F.mapQ_map_point_of_zeroEq h) := by
  simp only [KMap_eq_piMap, normalizedQ_eq_mapQ_of_zeroEq F h]

end CategoryTheory.ExactCategory.ExactFunctor
