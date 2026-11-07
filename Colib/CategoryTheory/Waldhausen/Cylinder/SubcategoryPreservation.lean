/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.SubcategoryZero
public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Functor.Pushouts
public import Colib.CategoryTheory.Waldhausen.Cylinder.Subcategory
public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.ZeroEndpoint
public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.Pushout
public import Colib.CategoryTheory.Waldhausen.ArrowCategory.Structure
public import Colib.CategoryTheory.Waldhausen.SplitComplexes.FunctorialFactorization

/-! # Actual middle-cylinder preservation in full complex subcategories

The original middle functor preserves zero objects and componentwise pushouts
along inherited admissible maps. It preserves both componentwise isomorphisms
and componentwise quasi-isomorphisms. All statements concern the unchanged
identity-cone cylinder and the actual full-subcategory maps.
-/
/-! Adapted from `Quillen.Waldhausen.Cylinder.SubcategoryPreservation`
at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CochainComplex
universe u v

open CochainComplex.SplitFactorization

namespace CategoryTheory.Waldhausen.SplitFactorization
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L →
    ∀ f : K ⟶ L, P (mappingCone f))

/-- The actual middle cylinder preserves displayed pointwise pushouts along
inherited admissible maps, with no global ambient-pushout closure assumption. -/
theorem subcategoryMiddleFunctor_map_isPushout
    {K L M N : Arrow P.FullSubcategory} {f : K ⟶ L} {g : K ⟶ M}
    {i : L ⟶ N} {j : M ⟶ N}
    (hf : ArrowCategory.cof (complexSubcategory P) f)
    (hL : IsPushout f.left g.left i.left j.left)
    (hR : IsPushout f.right g.right i.right j.right) :
    IsPushout ((subcategoryMiddleFunctor P hcone).map f)
      ((subcategoryMiddleFunctor P hcone).map g)
      ((subcategoryMiddleFunctor P hcone).map i)
      ((subcategoryMiddleFunctor P hcone).map j) := by
  apply IsPushout.of_map_of_faithful P.ι
  exact middleFunctor_map_isPushout
    ((ExactSubcategory.exactInclusion (abelianExactStructure (CochainComplex A ℤ))
      P).map_isPushout hf.1 hL)
    ((ExactSubcategory.exactInclusion (abelianExactStructure (CochainComplex A ℤ))
      P).map_isPushout hf.2 hR)

/-- The target quasi-isomorphism alone suffices for the original middle map. -/
theorem subcategoryMiddleFunctor_map_weak {f g : Arrow P.FullSubcategory} (α : f ⟶ g)
    (hα : (complexSubcategory P).weq α.right) :
    (complexSubcategory P).weq ((subcategoryMiddleFunctor P hcone).map α) := by
  let : QuasiIso (P.ι.mapArrow.map α).right := hα
  exact middleFunctor_map_quasiIso (P.ι.mapArrow.map α)

end CategoryTheory.Waldhausen.SplitFactorization
