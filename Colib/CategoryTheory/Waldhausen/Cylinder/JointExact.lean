/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.Waldhausen.Cylinder.JointFunctor
public import Colib.CategoryTheory.Waldhausen.Cylinder.JointSource

/-! # Exactness of the actual complex joint-cylinder functor

The domain is the entire arrow category with pointwise cofibrations, and the
target is the cofibration-arrow category with its genuine Reedy structure.
The theorem is proved for both isomorphism and quasi-isomorphism weak models,
using the unchanged cylinder maps, actual pushouts, and inherited admissibility.
-/
/-! Adapted from `Quillen.Waldhausen.Cylinder.JointExact`
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
  (hshift : ∀ K, P K → P (K⟦(1 : ℤ)⟧))

/-- Its source component is literally the actual endpoint-sum functor. -/
@[simp] theorem subcategoryJointFunctor_comp_source :
    subcategoryJointFunctor P hcone hshift ⋙ ExtensionCategory.source (complexSubcategory P) =
      subcategoryJointSourceFunctor P := rfl

/-- The original joint cylinder is genuinely exact for quasi-isomorphism weak maps. -/
theorem subcategoryJointFunctor_quasiExact :
    IsExact (ArrowCategory.waldhausenStructure (complexSubcategory P)).cof
      (ArrowCategory.waldhausenStructure (complexSubcategory P)).weq
      (ExtensionCategory.waldhausenStructure (complexSubcategory P)).cof
      (ExtensionCategory.waldhausenStructure (complexSubcategory P)).weq
      (subcategoryJointFunctor P hcone hshift) where
  zero h := ExtensionCategory.isZero_of_components (complexSubcategory P) _
    ((subcategoryJointSourceFunctor_quasiExact P).zero h)
    (subcategoryMiddleFunctor_zero P hcone h)
  cofibration α hα := subcategoryJointFunctor_map_cof_of_source P hcone hshift α hα.1
    ((subcategoryJointSourceFunctor_quasiExact P).cofibration α hα)
  weak α hα := ⟨(subcategoryJointSourceFunctor_quasiExact P).weak α hα,
    subcategoryMiddleFunctor_map_weak P hcone α hα.2⟩
  pushout hf h := by
    obtain ⟨hL, hR⟩ := ArrowCategory.pointwise_of_isPushout (complexSubcategory P) hf h
    apply IsPushout.of_map_of_faithful (ExtensionCategory.forget (complexSubcategory P))
    exact ExtensionCategory.arrow_isPushout _ _ _ _
      ((subcategoryJointSourceFunctor_quasiExact P).pushout hf h)
      (subcategoryMiddleFunctor_map_isPushout P hcone hf hL hR)

/-- The same original joint cylinder is exact for the isomorphism weak model.
The cofibration-arrow category is definitionally the same; only weak maps change. -/
theorem subcategoryJointFunctor_isoExact :
    let W := ofExactCategory (ExactSubcategory.exactStructure
      (abelianExactStructure (CochainComplex A ℤ)) P)
    IsExact (ArrowCategory.waldhausenStructure W).cof
      (ArrowCategory.waldhausenStructure W).weq
      (ExtensionCategory.waldhausenStructure W).cof
      (ExtensionCategory.waldhausenStructure W).weq
      (subcategoryJointFunctor P hcone hshift) where
  zero := (subcategoryJointFunctor_quasiExact P hcone hshift).zero
  cofibration := (subcategoryJointFunctor_quasiExact P hcone hshift).cofibration
  weak α hα := by
    let : IsIso α.left := hα.1
    let : IsIso α.right := hα.2
    let : IsIso α := Arrow.isIso_of_isIso_left_of_isIso_right α
    exact ExtensionCategory.weq_iso _ _
      (inferInstance : IsIso ((subcategoryJointFunctor P hcone hshift).map α))
  pushout := (subcategoryJointFunctor_quasiExact P hcone hshift).pushout

end CategoryTheory.Waldhausen.SplitFactorization
