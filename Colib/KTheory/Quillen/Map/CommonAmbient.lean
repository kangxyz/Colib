/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.KTheory.Quillen.Equivalence
public import Colib.Topology.Homotopy.HomotopyGroup.Equivalence

/-!
# Exact K-maps with a common realization universe

The original categories may have different morphism universes. If both
object types lie in the maximum of those universes, their Q-categories
already have the same object and morphism universes: a Q-arrow contains
an apex object. Thus the existing classifying-space and based-homotopy APIs
apply directly, without identifying realizations in different universes.
-/
@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
universe v₁ v₂
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.ExactCategory.ExactFunctor
open Topology

variable {C D : Type (max v₁ v₂)} [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D} (F : ExactFunctor EC ED)

/-- Zero-normalize the actual Q-functor in its common ambient universe. -/
def commonAmbientNormalizedQ : EC.QCategory ⥤ ED.QCategory :=
  rebaseFunctor F.mapQ (QConstruction.of _ _ (0 : C)) (QConstruction.of _ _ (0 : D))
    (ED.qIsoOfIso F.toFunctor.mapZeroObject)

@[simp] theorem commonAmbientNormalizedQ_map_point :
    classifyingSpaceMap F.commonAmbientNormalizedQ EC.kBasepoint = ED.kBasepoint :=
  rebaseFunctor_map_point F.mapQ _ _ _

/-- The actual based K-map in the shared realization universe. -/
def commonAmbientKMap (n : ℕ) : EC.K n →* ED.K n :=
  HomotopyGroup.piMap n (classifyingSpaceMap F.commonAmbientNormalizedQ).hom
    F.commonAmbientNormalizedQ_map_point

instance commonAmbientNormalizedQ_isEquivalence [F.mapQ.IsEquivalence] :
    F.commonAmbientNormalizedQ.IsEquivalence :=
  Functor.isEquivalence_of_iso (rebaseFunctorIso F.mapQ
    (QConstruction.of _ _ (0 : C)) (QConstruction.of _ _ (0 : D))
    (ED.qIsoOfIso F.toFunctor.mapZeroObject))

/-- A genuine categorical equivalence of Q-models gives a canonical K-group
equivalence even when the original categories have different hom universes. -/
def commonAmbientKEquiv [F.mapQ.IsEquivalence] (n : ℕ) : EC.K n ≃* ED.K n :=
  homotopyEquivPiEquiv (classifyingHomotopyEquivOfIsEquivalence F.commonAmbientNormalizedQ)
    F.commonAmbientNormalizedQ_map_point n

/-- The underlying monoid homomorphism of this K-equivalence. -/
@[simp] theorem commonAmbientKEquiv_coe [F.mapQ.IsEquivalence] (n : ℕ) :
    (↑(F.commonAmbientKEquiv n) : EC.K n →* ED.K n) = F.commonAmbientKMap n := rfl


end CategoryTheory.ExactCategory.ExactFunctor
