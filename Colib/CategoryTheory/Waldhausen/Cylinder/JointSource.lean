/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.JointSource
public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.Waldhausen.Cylinder.Subcategory
public import Colib.CategoryTheory.Waldhausen.ArrowCategory.Structure
public import Colib.CategoryTheory.Waldhausen.Additivity.SplitSequence
public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.ExactTransport

/-! # The actual joint-endpoint source functor

Objects are the original ambient biproduct of the source and target, with
membership supplied by extension closure. Maps are the literal ambient
`biprod.map`. Its genuine coproduct universal property identifies this functor
with the already exact sum of the two actual arrow evaluations. This proves
structural exactness for any Waldhausen structure on the same full subcategory,
in particular for both inherited isomorphism and quasi-isomorphism structures.
-/
/-! Adapted from `Quillen.Waldhausen.Cylinder.JointSource`
at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v

open CochainComplex.SplitFactorization

namespace CategoryTheory.Waldhausen.SplitFactorization
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]

variable [P.IsClosedUnderFiniteProducts]

/-- Genuine source exactness, for any actual Waldhausen structure on the full subcategory. -/
theorem subcategoryJointSourceFunctor_isExact (W : Structure P.FullSubcategory) :
    IsExact (ArrowCategory.waldhausenStructure W).cof (ArrowCategory.waldhausenStructure W).weq
      W.cof W.weq (subcategoryJointSourceFunctor P) :=
  ExtensionCategory.isExact_of_natIso (ArrowCategory.waldhausenStructure W) W
    (Additivity.sumFunctor_isExact (ArrowCategory.waldhausenStructure W) W
      (ArrowCategory.source_exact W) (ArrowCategory.target_exact W))
        (subcategoryJointSourceSumIso P)

variable [P.ContainsZero] [P.IsClosedUnderIsomorphisms]

/-- Specialization to inherited admissible cofibrations and actual isomorphisms. -/
theorem subcategoryJointSourceFunctor_isoExact :
    let W := ofExactCategory (ExactSubcategory.exactStructure
      (abelianExactStructure (CochainComplex A ℤ)) P)
    IsExact (ArrowCategory.waldhausenStructure W).cof (ArrowCategory.waldhausenStructure W).weq
      W.cof W.weq (subcategoryJointSourceFunctor P) :=
  subcategoryJointSourceFunctor_isExact P _

/-- Specialization to inherited admissible cofibrations and actual quasi-isomorphisms. -/
theorem subcategoryJointSourceFunctor_quasiExact :
    IsExact (ArrowCategory.waldhausenStructure (complexSubcategory P)).cof
      (ArrowCategory.waldhausenStructure (complexSubcategory P)).weq
      (complexSubcategory P).cof (complexSubcategory P).weq (subcategoryJointSourceFunctor P) :=
  subcategoryJointSourceFunctor_isExact P _

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms] in
/-- Actual displayed component pushouts give the displayed joint-source pushout. -/
theorem subcategoryJointSourceFunctor_map_isPushout (W : Structure P.FullSubcategory)
    {F G H T : Arrow P.FullSubcategory} {f : F ⟶ G} {g : F ⟶ H} {i : G ⟶ T} {j : H ⟶ T}
    (hf : W.cof f.left ∧ W.cof f.right)
    (hL : IsPushout f.left g.left i.left j.left)
    (hR : IsPushout f.right g.right i.right j.right) :
    IsPushout ((subcategoryJointSourceFunctor P).map f) ((subcategoryJointSourceFunctor P).map g)
      ((subcategoryJointSourceFunctor P).map i) ((subcategoryJointSourceFunctor P).map j) :=
  (subcategoryJointSourceFunctor_isExact P W).pushout hf
    (ArrowCategory.isPushout_of_pointwise f g i j hL hR)

end CategoryTheory.Waldhausen.SplitFactorization
