/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Algebra.Group.ExactTransport
public import Colib.CategoryTheory.SmallModel.Localization
public import Colib.KTheory.Quillen.SmallModel.Abelian
public import Colib.KTheory.Quillen.Localization.Serre.Target

/-!
# Canonical connective localization on actual small exact models

An actual exact functor between essentially small abelian categories which is
a Serre localization yields the connective localization sequence for its original
`smallKMap`. All categorical quotient and exact-structure comparisons are proved;
the only localization hypothesis here concerns the actual input functor.

Adapted from `Quillen/GTheory/SmallModelLocalization.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The native descended functor is the
literal `ExactFunctor.smallModel.toFunctor`, without a separate functor model.
-/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe w v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
attribute [local instance] Abelian.hasFiniteBiproducts
namespace CategoryTheory.ExactCategory.SmallModelGLocalization

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  (F : ExactFunctor (abelianExactStructure C) (abelianExactStructure D))
  [PreservesFiniteLimits F.toFunctor] [PreservesFiniteColimits F.toFunctor]
  [F.toFunctor.IsLocalization F.toFunctor.kernel.isoModSerre]

/-- The actual kernel of the descended exact functor. -/
abbrev supported : ObjectProperty (SmallModel.{w} C) := F.smallModel.toFunctor.kernel

/-- The genuine supported K-term in the chosen small model. -/
abbrev SupportedK (n : ℕ) :=
  (abelianExactStructure (supported F).FullSubcategory).K n

/-- The canonical inclusion, followed by the identity exact-structure comparison. -/
def inclusionKMap (n : ℕ) : SupportedK F n →* (abelianExactStructure C).SmallK n :=
  (SmallModelLocalization.standardKEquiv C n).symm.toMonoidHom.comp
    (Abelian.Devissage.KMap (supported F) n)

/-- The boundary from the actual target, with the canonical small exact-structure comparison. -/
def connectingHom (n : ℕ) : (abelianExactStructure D).SmallK (n + 1) →* SupportedK F n :=
  (SerreLocalization.actualConnectingHom (supported F)
    (F.smallModel.toFunctor) n).comp
      (SmallModelLocalization.standardKEquiv D (n + 1)).toMonoidHom

lemma KMap_comparison (n : ℕ) (x : (abelianExactStructure C).SmallK n) :
    SmallModelLocalization.standardKEquiv D n (F.smallKMap n x) =
      SerreLocalization.KMap (supported F) (F.smallModel.toFunctor) n
        (SmallModelLocalization.standardKEquiv C n x) := by
  exact DFunLike.congr_fun (SmallModelLocalization.smallKMap_comparison F n) x

/-- Exactness at the original canonical small-model K-group of C. -/
theorem inclusion_range_eq_KMap_ker (n : ℕ) :
    (inclusionKMap F n).range = (F.smallKMap n).ker := by
  apply MonoidHom.range_eq_ker_of_equiv (inclusionKMap F n) (F.smallKMap n)
    (Abelian.Devissage.KMap (supported F) n)
    (SerreLocalization.KMap (supported F) (F.smallModel.toFunctor) n)
    (MulEquiv.refl _) (SmallModelLocalization.standardKEquiv C n)
    (SmallModelLocalization.standardKEquiv D n)
  · intro a
    exact (SmallModelLocalization.standardKEquiv C n).apply_symm_apply _
  · exact KMap_comparison F n
  · exact SerreLocalization.actual_inclusion_range_eq_KMap_ker _ _ n

/-- Exactness at the original canonical small-model K-group of D. -/
theorem KMap_range_eq_connecting_ker (n : ℕ) :
    (F.smallKMap (n + 1)).range = (connectingHom F n).ker := by
  apply MonoidHom.range_eq_ker_of_equiv (F.smallKMap (n + 1)) (connectingHom F n)
    (SerreLocalization.KMap (supported F) (F.smallModel.toFunctor) (n + 1))
    (SerreLocalization.actualConnectingHom (supported F)
      (F.smallModel.toFunctor) n)
    (SmallModelLocalization.standardKEquiv C (n + 1))
    (SmallModelLocalization.standardKEquiv D (n + 1)) (MulEquiv.refl _)
  · exact KMap_comparison F (n + 1)
  · intro a; rfl
  · exact SerreLocalization.actual_KMap_range_eq_connecting_ker _ _ n

/-- Exactness at the actual small-model supported K-term. -/
theorem connecting_range_eq_inclusion_ker (n : ℕ) :
    (connectingHom F n).range = (inclusionKMap F n).ker := by
  apply MonoidHom.range_eq_ker_of_equiv (connectingHom F n) (inclusionKMap F n)
    (SerreLocalization.actualConnectingHom (supported F)
      (F.smallModel.toFunctor) n)
    (Abelian.Devissage.KMap (supported F) n)
    (SmallModelLocalization.standardKEquiv D (n + 1)) (MulEquiv.refl _)
    (SmallModelLocalization.standardKEquiv C n)
  · intro a; rfl
  · intro a
    exact (SmallModelLocalization.standardKEquiv C n).apply_symm_apply _
  · exact SerreLocalization.actual_connecting_range_eq_inclusion_ker _ _ n

/-- The original canonical small-model K₀ map is surjective. -/
theorem KZero_surjective : Function.Surjective (F.smallKMap 0) := by
  intro y
  obtain ⟨x, hx⟩ := SerreLocalization.actualKZero_surjective (supported F)
    (F.smallModel.toFunctor) (SmallModelLocalization.standardKEquiv D 0 y)
  refine ⟨(SmallModelLocalization.standardKEquiv C 0).symm x,
    (SmallModelLocalization.standardKEquiv D 0).injective ?_⟩
  rw [KMap_comparison, MulEquiv.apply_symm_apply, hx]

/-- The complete canonical connective localization sequence on actual small models. -/
theorem localization_longExact :
    (∀ n, (inclusionKMap F n).range = (F.smallKMap n).ker) ∧
    (∀ n, (F.smallKMap (n + 1)).range = (connectingHom F n).ker) ∧
    (∀ n, (connectingHom F n).range = (inclusionKMap F n).ker) ∧
    Function.Surjective (F.smallKMap 0) :=
  ⟨inclusion_range_eq_KMap_ker F, KMap_range_eq_connecting_ker F,
    connecting_range_eq_inclusion_ker F, KZero_surjective F⟩

end CategoryTheory.ExactCategory.SmallModelGLocalization

attribute [colib_tag "COL-0272",
  colib_ref "WeibelKBook" "V, Theorem 5.1, page 35" "adaptation"
    "The original small-model K-map and actual transported path-space boundary"]
  CategoryTheory.ExactCategory.SmallModelGLocalization.inclusion_range_eq_KMap_ker
  CategoryTheory.ExactCategory.SmallModelGLocalization.KMap_range_eq_connecting_ker
  CategoryTheory.ExactCategory.SmallModelGLocalization.connecting_range_eq_inclusion_ker
  CategoryTheory.ExactCategory.SmallModelGLocalization.KZero_surjective
  CategoryTheory.ExactCategory.SmallModelGLocalization.localization_longExact
