/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Ext
public import Colib.CategoryTheory.ExactCategory.Subcategory
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.CategoryTheory.ExactCategory.Resolution.Closure
public import Colib.CategoryTheory.ExactCategory.Equivalence

/-!
# Canonical comparisons for nested inherited exact subcategories

Flattening a nested full subcategory is a genuine exact equivalence, and the
factorization through it retains the original inclusion maps. This supplies
the categorical bookkeeping for adjacent resolution-length strata.
-/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.ExactCategory.Resolution
variable {C : Type u} [SmallCategory C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (P Q : ObjectProperty C)
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [E.IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms] [E.IsExtensionClosed Q]
  [Q.IsClosedUnderFiniteProducts]

instance inclusionOfLE_additive (h : P ≤ Q) : (ObjectProperty.ιOfLE h).Additive where
  map_add := by intros; rfl

/-- The canonical exact inclusion for an inequality of inherited properties. -/
def exactInclusionOfLE (h : P ≤ Q) :
    ExactFunctor (ExactSubcategory.exactStructure E P) (ExactSubcategory.exactStructure E Q) where
  toFunctor := ObjectProperty.ιOfLE h
  map_conflation _ hS := hS

@[simp] theorem exactInclusionOfLE_comp (h : P ≤ Q) :
    (exactInclusionOfLE E P Q h).comp (ExactSubcategory.exactInclusion E Q) =
      ExactSubcategory.exactInclusion E P := rfl

instance restrictedProperty_extensionClosed :
    (ExactSubcategory.exactStructure E Q).IsExtensionClosed (P.inverseImage Q.ι) where
  prop_middle hS h₁ h₃ := CategoryTheory.ExactCategory.ExactStructure.IsExtensionClosed.prop_middle
    (E := E) hS h₁ h₃

instance restrictedProperty_finiteProducts :
    (P.inverseImage Q.ι).IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape _ _ := inferInstance

instance restrictedProperty_kernelClosed [E.IsKernelClosed P] :
    (ExactSubcategory.exactStructure E Q).IsKernelClosed (P.inverseImage Q.ι) where
  prop_kernel hS h₂ h₃ := CategoryTheory.ExactCategory.ExactStructure.IsKernelClosed.prop_kernel (E
    := E) hS h₂ h₃

/-- The original smaller category, lifted into the nested full subcategory. -/
def nestedLift (h : P ≤ Q) : P.FullSubcategory ⥤ (P.inverseImage Q.ι).FullSubcategory :=
  (P.inverseImage Q.ι).lift (ObjectProperty.ιOfLE h) (fun X => X.property)

instance nestedLift_full (h : P ≤ Q) : (nestedLift P Q h).Full := by
  dsimp [nestedLift]
  infer_instance

instance nestedLift_faithful (h : P ≤ Q) : (nestedLift P Q h).Faithful := by
  dsimp [nestedLift]
  infer_instance

instance nestedLift_additive (h : P ≤ Q) : (nestedLift P Q h).Additive := by
  dsimp [nestedLift]
  infer_instance

instance nestedLift_essSurj (h : P ≤ Q) : (nestedLift P Q h).EssSurj where
  mem_essImage Z := ⟨⟨Z.obj.obj, Z.property⟩, ⟨Iso.refl _⟩⟩

instance nestedLift_isEquivalence (h : P ≤ Q) : (nestedLift P Q h).IsEquivalence := {}

/-- The nested lift is exact for the genuinely inherited structures. -/
def nestedLiftExact (h : P ≤ Q) :
    ExactFunctor (ExactSubcategory.exactStructure E P)
      (ExactSubcategory.exactStructure (ExactSubcategory.exactStructure E Q)
        (P.inverseImage Q.ι)) where
  toFunctor := nestedLift P Q h
  map_conflation _ hS := hS

instance nestedLift_asEquivalence_additive (h : P ≤ Q) :
    (nestedLift P Q h).asEquivalence.functor.Additive :=
  inferInstanceAs (nestedLift P Q h).Additive

instance nestedLiftExact_isEquivalence (h : P ≤ Q) :
    (nestedLiftExact E P Q h).toFunctor.IsEquivalence :=
  inferInstanceAs (nestedLift P Q h).IsEquivalence

/-- Flattening reflects conflations, not only the underlying category. -/
theorem nestedLift_ofEquivalence (h : P ≤ Q) :
    (ExactSubcategory.exactStructure (ExactSubcategory.exactStructure E Q)
      (P.inverseImage Q.ι)).ofEquivalence (nestedLift P Q h).asEquivalence =
      ExactSubcategory.exactStructure E P := by
  apply CategoryTheory.ExactCategory.ExactStructure.ext_conflation
  funext S
  rfl

@[simp] theorem nestedLift_factor (h : P ≤ Q) :
    (nestedLiftExact E P Q h).comp
      (ExactSubcategory.exactInclusion (ExactSubcategory.exactStructure E Q) (P.inverseImage Q.ι)) =
        exactInclusionOfLE E P Q h := rfl

end CategoryTheory.ExactCategory.Resolution
