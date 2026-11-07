/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.KTheory.Quillen.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.QIsomorphisms
public import Colib.Topology.ClassifyingSpace.PointedFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Exact-functor maps on zero-based Quillen K-groups

The canonical `mapZeroObject` isomorphism determines the rebasing of the
actual induced Q-functor. The resulting map is based at the vertex of the
original zero object and acts on the actual `(n + 1)`st homotopy group.
This module proves identity, not composition or natural-isomorphism invariance.

## Implementation provenance

Extracted from `Quillen/KTheory/Map/Basic.lean` and
`Quillen/Topology/ClassifyingSpace/PointedFunctor.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The source maps, basepoints,
universes and degree shift are retained. Only ownership and lower imports change.
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.QConstruction.CompatibleFunctor

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [HasFiniteBiproducts C]
  [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactCategory.ExactStructure C} {ED : ExactCategory.ExactStructure D}

/-- A Q-compatible functor with a specified zero-object isomorphism induces
an actual homomorphism between the K-groups based at the chosen zero objects.
The construction uses the explicitly rebased Q-functor. -/
def kMapWithZeroIso
    (F : QConstruction.CompatibleFunctor EC.deflation EC.inflation ED.deflation ED.inflation)
    (e : F.toFunctor.obj (0 : C) ≅ (0 : D)) (n : ℕ) : EC.K n →* ED.K n :=
  pointedShiftedHomotopyGroupMap F.mapQ
    (QConstruction.of EC.deflation EC.inflation (0 : C))
    (QConstruction.of ED.deflation ED.inflation (0 : D)) (ED.qIsoOfIso e) n


end CategoryTheory.QConstruction.CompatibleFunctor

namespace CategoryTheory.ExactCategory.ExactFunctor

variable {C : Type u} {D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [HasFiniteBiproducts C]
  [Preadditive D] [HasFiniteBiproducts D]
  {EC : CategoryTheory.ExactCategory.ExactStructure C} {ED :
    CategoryTheory.ExactCategory.ExactStructure D}

/-- The homomorphism of genuine Quillen K-groups associated to an exact
functor, with both basepoints the chosen zero objects. -/
def KMap (F : ExactFunctor EC ED) (n : ℕ) : EC.K n →* ED.K n :=
  F.toQCompatibleFunctor.kMapWithZeroIso F.toFunctor.mapZeroObject n

set_option backward.isDefEq.respectTransparency false in
/-- The identity exact functor induces the identity on every K-group. -/
@[simp]
theorem KMap_id (E : CategoryTheory.ExactCategory.ExactStructure C) (n : ℕ) :
    (CategoryTheory.ExactCategory.ExactFunctor.id E).KMap n = MonoidHom.id (E.K n) := by
  have hz : (CategoryTheory.ExactCategory.ExactFunctor.id E).toFunctor.mapZeroObject = Iso.refl (0 :
    C) := by
    apply Iso.ext
    apply Subsingleton.elim
  change pointedShiftedHomotopyGroupMap (CategoryTheory.ExactCategory.ExactFunctor.id E).mapQ
    (QConstruction.of E.deflation E.inflation (0 : C))
    (QConstruction.of E.deflation E.inflation (0 : C))
    (E.qIsoOfIso (CategoryTheory.ExactCategory.ExactFunctor.id E).toFunctor.mapZeroObject) n = _
  rw [hz]
  change pointedShiftedHomotopyGroupMap (CategoryTheory.ExactCategory.ExactFunctor.id E).mapQ
    (QConstruction.of E.deflation E.inflation (0 : C))
    (QConstruction.of E.deflation E.inflation (0 : C))
    (Iso.refl (QConstruction.of E.deflation E.inflation (0 : C))) n = _
  have hF : rebaseFunctor (CategoryTheory.ExactCategory.ExactFunctor.id E).mapQ
      (QConstruction.of E.deflation E.inflation (0 : C))
      (QConstruction.of E.deflation E.inflation (0 : C)) (Iso.refl _) =
      𝟭 (QConstruction E.deflation E.inflation) :=
    (rebaseFunctor_refl (CategoryTheory.ExactCategory.ExactFunctor.id E).mapQ _).trans
      (CategoryTheory.ExactCategory.ExactFunctor.mapQ_id E)
  have hT : classifyingSpaceMap (rebaseFunctor (CategoryTheory.ExactCategory.ExactFunctor.id E).mapQ
      (QConstruction.of E.deflation E.inflation (0 : C))
      (QConstruction.of E.deflation E.inflation (0 : C)) (Iso.refl _)) =
      𝟙 (ClassifyingSpace (QConstruction E.deflation E.inflation)) := by
    rw [hF, classifyingSpaceMap_id]
  apply MonoidHom.ext
  intro a
  change HomotopyGroup.map (classifyingSpaceMap (rebaseFunctor
    (CategoryTheory.ExactCategory.ExactFunctor.id E).mapQ
      (QConstruction.of E.deflation E.inflation (0 : C))
      (QConstruction.of E.deflation E.inflation (0 : C)) (Iso.refl _))).hom _ a = a
  simpa only [hT, TopCat.hom_id] using HomotopyGroup.map_id a


end CategoryTheory.ExactCategory.ExactFunctor

attribute [colib_tag "COL-0055",
  colib_ref "WeibelKBook"
    "IV, paragraph following Definition 6.3, induced K-group map" "adaptation"
    "The zero-based induced map and identity law, without composition or invariance"]
  CategoryTheory.ExactCategory.ExactFunctor.KMap
  CategoryTheory.ExactCategory.ExactFunctor.KMap_id

attribute [colib_ref "Quillen1973"
    "Section 2, equation (6) and following paragraph, p. 103" "adaptation"
    "Actual zero-based map of an exact functor and its identity law"]
  CategoryTheory.ExactCategory.ExactFunctor.KMap
  CategoryTheory.ExactCategory.ExactFunctor.KMap_id
