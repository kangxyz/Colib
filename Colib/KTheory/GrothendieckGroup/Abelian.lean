/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.KTheory.GrothendieckGroup.Basic
public import StacksCore.CategoryTheory.GrothendieckGroup.Basic

/-!
# Comparing the abelian exact structure with the categorical Grothendieck group

For the standard exact structure of an abelian category, the conflation presentation
has exactly the short-exact-sequence relations used by the pinned Stacks Core group.
The equivalence below identifies the actual object generators in both directions.
It makes no identification with a homotopy group of the Q-construction.
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ExactCategory

variable (C : Type u) [Category.{v} C] [Abelian C]

attribute [local instance] Abelian.hasFiniteBiproducts

/-- The comparison sends each conflation-presentation generator to the same
object's class in the Stacks Core Grothendieck group. -/
def abelianGrothendieckToStacks :
    (abelianExactStructure C).GrothendieckGroup →+ CategoryTheory.GrothendieckGroup C :=
  (abelianExactStructure C).grothendieckLift CategoryTheory.GrothendieckGroup.of
    (fun _ hS => CategoryTheory.GrothendieckGroup.additivity hS)

/-- The inverse comparison uses the additivity of the conflation presentation. -/
def stacksToAbelianGrothendieck :
    CategoryTheory.GrothendieckGroup C →+ (abelianExactStructure C).GrothendieckGroup :=
  CategoryTheory.GrothendieckGroup.lift (abelianExactStructure C).grothendieckClass
    (fun _ hS => (abelianExactStructure C).grothendieckClass_additive hS)

@[simp]
lemma abelianGrothendieckToStacks_class (X : C) :
    abelianGrothendieckToStacks C ((abelianExactStructure C).grothendieckClass X) =
      CategoryTheory.GrothendieckGroup.of X := by
  exact (abelianExactStructure C).grothendieckLift_class _ _ X

@[simp]
lemma stacksToAbelianGrothendieck_of (X : C) :
    stacksToAbelianGrothendieck C (CategoryTheory.GrothendieckGroup.of X) =
      (abelianExactStructure C).grothendieckClass X := by
  simp [stacksToAbelianGrothendieck]

/-- For an abelian category, the standard exact structure's algebraic K₀ is
canonically equivalent to the pinned Stacks Core Grothendieck group. -/
def abelianGrothendieckEquiv :
    (abelianExactStructure C).GrothendieckGroup ≃+ CategoryTheory.GrothendieckGroup C where
  toFun := abelianGrothendieckToStacks C
  invFun := stacksToAbelianGrothendieck C
  left_inv x := by
    have h : (stacksToAbelianGrothendieck C).comp (abelianGrothendieckToStacks C) =
        AddMonoidHom.id _ := by
      apply (abelianExactStructure C).grothendieck_hom_ext
      intro X
      simp
    exact DFunLike.congr_fun h x
  right_inv x := by
    have h : (abelianGrothendieckToStacks C).comp (stacksToAbelianGrothendieck C) =
        AddMonoidHom.id _ := by
      apply CategoryTheory.GrothendieckGroup.hom_ext
      intro X
      simp
    exact DFunLike.congr_fun h x
  map_add' := (abelianGrothendieckToStacks C).map_add

/-- The canonical comparison preserves each object generator. -/
@[simp]
lemma abelianGrothendieckEquiv_class (X : C) :
    abelianGrothendieckEquiv C ((abelianExactStructure C).grothendieckClass X) =
      CategoryTheory.GrothendieckGroup.of X :=
  abelianGrothendieckToStacks_class C X

/-- The inverse comparison also preserves each object generator. -/
@[simp]
lemma abelianGrothendieckEquiv_symm_of (X : C) :
    (abelianGrothendieckEquiv C).symm (CategoryTheory.GrothendieckGroup.of X) =
      (abelianExactStructure C).grothendieckClass X :=
  stacksToAbelianGrothendieck_of C X

end CategoryTheory.ExactCategory

attribute [colib_tag "COL-0019",
  stacks 02MU "generator-preserving comparison for the canonical abelian exact structure",
  colib_ref "WeibelKBook" "II, Definitions 6.1.1 and 7.1" "comparison"
    "The canonical abelian exact structure and the categorical short-exact-sequence presentation"]
  CategoryTheory.ExactCategory.abelianGrothendieckEquiv

attribute [colib_tag "COL-0019"]
  CategoryTheory.ExactCategory.abelianGrothendieckEquiv_class
  CategoryTheory.ExactCategory.abelianGrothendieckEquiv_symm_of
