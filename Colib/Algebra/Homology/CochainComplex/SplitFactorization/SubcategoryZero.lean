/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.JointSubcategory
public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.ZeroEndpoint
public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.Pushout

/-!
# Zero preservation of the restricted middle-object functor

The original identity-cone middle functor preserves actual zero endpoints and
zero arrows in the stated cone-closed full complex subcategory.
-/
/-! Adapted from `Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.SubcategoryZero`
at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CochainComplex
universe u v

namespace CochainComplex.SplitFactorization
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]
  (hcone : ∀ {K L : CochainComplex A ℤ}, P K → P L →
    ∀ f : K ⟶ L, P (mappingCone f))

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderFiniteProducts] in
/-- A cylinder with two genuinely zero endpoints is genuinely zero. -/
theorem subcategoryMiddleFunctor_obj_isZero {f : Arrow P.FullSubcategory}
    (hl : IsZero f.left) (hr : IsZero f.right) :
    IsZero ((subcategoryMiddleFunctor P hcone).obj f) := by
  have hm : IsZero ((subcategoryMiddleFunctor P hcone).obj f).obj :=
    (P.ι.map_isZero hr).of_iso
      (projectionIsoOfIsZeroSource f.hom.hom (P.ι.map_isZero hl))
  rw [IsZero.iff_id_eq_zero]
  apply ObjectProperty.hom_ext
  exact hm.eq_of_src _ _

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderFiniteProducts] in
/-- Every genuine zero object of the entire arrow category is preserved. -/
theorem subcategoryMiddleFunctor_zero {f : Arrow P.FullSubcategory} (hf : IsZero f) :
    IsZero ((subcategoryMiddleFunctor P hcone).obj f) :=
  subcategoryMiddleFunctor_obj_isZero P hcone
    (by
      rw [IsZero.iff_id_eq_zero]
      exact congrArg (fun k => k.left)
        (hf.eq_of_src (𝟙 f) (Arrow.homMk 0 0 (by simp))))
    (by
      rw [IsZero.iff_id_eq_zero]
      exact congrArg (fun k => k.right)
        (hf.eq_of_src (𝟙 f) (Arrow.homMk 0 0 (by simp))))

end CochainComplex.SplitFactorization
