/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Cofinality.GeneralKZeroValue
public import Colib.KTheory.Waldhausen.Cofinality.GeneralDense

/-! # Dense cofinality with its actual complement-class K-zero endpoint

The genuine coarse value map sends each original object loop to its original
common-complement class. Every such class has an actual object representative,
so the value map is bijective. Composing with the unchanged changeWeak KMap
identifies the original dense-inclusion image with the actual class kernel in
independent object and morphism universes.

This combines the original maps of `Quillen/Waldhausen/Cofinality/DenseKZero.lean`
and `GeneralKZeroValue.lean` at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The general-universe proof retains the existing AsSmall transport explicitly.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Waldhausen.Fibration
universe u v

namespace CategoryTheory.Waldhausen.Cofinality.DenseCofiberData

variable {C : Type u} [Category.{v} C] {W : Structure C} [HasBinaryCoproducts C]
  {P : ObjectProperty C} (h : DenseCofiberData W P)
  (D : RowFactorization.JointData (NestedWeakEquivalences.refl W))

/-- The actual coarse grading gives the original complement class of every object. -/
def coarseClassKZeroMap : h.grading.coarseStructure.K 0 →* Multiplicative h.Classes :=
  h.grading.coarseKZeroValueMap D.reflexiveAsSmall.sourceFactorization

@[simp] theorem coarseClassKZeroMap_objectClass (A : C) :
    h.coarseClassKZeroMap D (h.grading.coarseStructure.kZeroObjectClass A) =
      Multiplicative.ofAdd (h.classOf A) :=
  h.grading.coarseKZeroValueMap_objectClass D.reflexiveAsSmall.sourceFactorization A

/-- No complement class is lost when retaining the actual original coarse K-zero group. -/
theorem coarseClassKZeroMap_bijective : Function.Bijective (h.coarseClassKZeroMap D) := by
  refine ⟨h.grading.coarseKZeroValueMap_injective D.reflexiveAsSmall.sourceFactorization, ?_⟩
  intro a
  obtain ⟨A, hA⟩ := h.classOf_surjective a.toAdd
  exact ⟨h.grading.coarseStructure.kZeroObjectClass A,
    (h.coarseClassKZeroMap_objectClass D A).trans (congrArg Multiplicative.ofAdd hA)⟩

/-- The original coarse value homomorphism itself is the complement-class equivalence. -/
def coarseClassKZeroEquiv : h.grading.coarseStructure.K 0 ≃* Multiplicative h.Classes :=
  MulEquiv.ofBijective (h.coarseClassKZeroMap D) (h.coarseClassKZeroMap_bijective D)

@[simp] theorem coarseClassKZeroEquiv_coe :
    (h.coarseClassKZeroEquiv D : h.grading.coarseStructure.K 0 →* Multiplicative h.Classes) =
      h.coarseClassKZeroMap D := rfl

/-- The exact original fine-to-coarse KMap followed by the original complement value map. -/
def classKZeroMapGeneral : W.K 0 →* Multiplicative h.Classes :=
  (h.coarseClassKZeroMap D).comp (KMap (changeWeak_exact h.grading.nested) 0)

@[simp] theorem classKZeroMapGeneral_objectClass (A : C) :
    h.classKZeroMapGeneral D (W.kZeroObjectClass A) = Multiplicative.ofAdd (h.classOf A) := by
  change h.coarseClassKZeroMap D
    (KMap (changeWeak_exact h.grading.nested) 0 (W.kZeroObjectClass A)) = _
  rw [KMap_kZeroObjectClass]
  exact h.coarseClassKZeroMap_objectClass D A

/-- The original complement-class obstruction has exactly the actual changeWeak kernel. -/
theorem classKZeroMapGeneral_ker :
    (h.classKZeroMapGeneral D).ker = (KMap (changeWeak_exact h.grading.nested) 0).ker := by
  ext x
  change h.coarseClassKZeroMap D (KMap (changeWeak_exact h.grading.nested) 0 x) = 1 ↔
    KMap (changeWeak_exact h.grading.nested) 0 x = 1
  constructor
  · intro hx
    exact (h.coarseClassKZeroMap_bijective D).injective
      (hx.trans (map_one (h.coarseClassKZeroMap D)).symm)
  · intro hx
    rw [hx, map_one]

variable (hs : RowFactorization.SecondEndpointSection (NestedWeakEquivalences.refl W) D)

include hs in
/-- The original dense K-zero tail ends in the actual complement-class group. -/
@[colib_tag "COL-0268"]
theorem classKZero_exact_general : Function.Injective (KMap h.inclusion_exact 0) ∧
    (KMap h.inclusion_exact 0).range = (h.classKZeroMapGeneral D).ker ∧
    Function.Surjective (h.classKZeroMapGeneral D) := by
  obtain ⟨hi, hk, hs⟩ := h.inclusion_KZero_exact_general D hs
  exact ⟨hi, hk.trans (h.classKZeroMapGeneral_ker D).symm,
    (h.coarseClassKZeroMap_bijective D).surjective.comp hs⟩

/-- In matching universes, the general obstruction is the same original class homomorphism. -/
theorem classKZeroMapGeneral_eq {C₀ : Type u} [SmallCategory C₀] {W₀ : Structure C₀}
    [HasBinaryCoproducts C₀] {P₀ : ObjectProperty C₀} (h₀ : DenseCofiberData W₀ P₀)
    (D₀ : RowFactorization.JointData (NestedWeakEquivalences.refl W₀)) :
    h₀.classKZeroMapGeneral D₀ = h₀.classKZeroMap D₀ := by
  apply AlgebraicGrothendieck.kZero_hom_ext W₀
  intro A
  rw [classKZeroMapGeneral_objectClass]
  change _ = (h₀.classRangeEquiv D₀.sourceFactorization).toMultiplicative
    (h₀.grading.coarseKZeroEquiv D₀.sourceFactorization
      (KMap (changeWeak_exact h₀.grading.nested) 0 (W₀.kZeroObjectClass A)))
  rw [KMap_kZeroObjectClass]
  exact (congrArg (h₀.classRangeEquiv D₀.sourceFactorization).toMultiplicative
    (h₀.grading.coarseKZeroEquiv_objectClass D₀.sourceFactorization A)).symm

end CategoryTheory.Waldhausen.Cofinality.DenseCofiberData
