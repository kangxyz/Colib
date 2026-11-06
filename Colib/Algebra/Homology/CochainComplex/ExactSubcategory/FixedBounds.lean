/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Pullbacks
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.TruncationTransformations

/-! # Actual fixed-bound truncation endpoints

The strictly term-bounded acyclic stratum inherits its exact structure by
proved extension closure. Restricted canonical truncation is zero below
the lower bound and naturally the original inclusion at the upper bound.
The endpoint isomorphisms use actual zero objects and original inclusions.
-/
/-! Adapted from
`Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.FixedBounds`
at pinned Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ZeroObject
universe v u
namespace CochainComplex

attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Specified strict term bounds, including zero terms at every outside index. -/
def HasTermBounds (K : CochainComplex A ℤ) (a b : ℤ) : Prop :=
  ∀ i, i < a ∨ b < i → IsZero (K.X i)

/-- Fixed source bounds identify the native strict support conditions at
exactly the same lower and upper integers. -/
theorem hasTermBounds_iff_isStrictlyGE_isStrictlyLE (K : CochainComplex A ℤ) (a b : ℤ) :
    HasTermBounds K a b ↔ K.IsStrictlyGE a ∧ K.IsStrictlyLE b := by
  constructor
  · intro h
    exact ⟨(K.isStrictlyGE_iff a).2 (fun n hn ↦ h n (Or.inl hn)),
      (K.isStrictlyLE_iff b).2 (fun n hn ↦ h n (Or.inr hn))⟩
  · rintro ⟨ha, hb⟩ n hn
    exact hn.elim (fun h ↦ (K.isStrictlyGE_iff a).1 ha n h)
      (fun h ↦ (K.isStrictlyLE_iff b).1 hb n h)

/-- Actual truncation is zero below a specified lower term bound. -/
theorem truncLE_isZero_below_bound (K : CochainComplex A ℤ) (a b n : ℤ)
    (hK : HasTermBounds K a b) (hn : n < a) : IsZero (K.truncLE n) := by
  rw [IsZero.iff_id_eq_zero]
  ext i
  by_cases hi : n < i
  · exact ((K.truncLE n).isZero_of_isStrictlyLE n i hi).eq_of_src _ _
  · let : Mono ((K.ιTruncLE n).f i) := (truncationDegree_shortExact K n i).mono_f
    exact (IsZero.of_mono ((K.ιTruncLE n).f i) (hK i (Or.inl (by omega)))).eq_of_src _ _

/-- The original truncation inclusion is invertible at every specified upper bound. -/
theorem truncLE_inclusion_isIso_above_bound (K : CochainComplex A ℤ) (a b n : ℤ)
    (hK : HasTermBounds K a b) (hn : b ≤ n) : IsIso (K.ιTruncLE n) := by
  let : K.IsStrictlyLE n := (K.isStrictlyLE_iff n).2 (fun i hi ↦ hK i (Or.inr (by omega)))
  exact (K.isIso_ιTruncLE_iff n).2 inferInstance

variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsKernelClosed P]

/-- The actual fixed-bound full subcategory of bounded acyclic complexes. -/
def fixedAcyclicBounds (a b : ℤ) : ObjectProperty (boundedAcyclic P).FullSubcategory :=
  fun K ↦ HasTermBounds K.obj a b

instance fixedAcyclicBounds_containsZero (a b : ℤ) : (fixedAcyclicBounds P a b).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, fun i _ ↦
    (eval A (ComplexShape.up ℤ) i).map_isZero ((boundedAcyclic P).ι.map_isZero (isZero_zero _))⟩

instance fixedAcyclicBounds_closedUnderIsomorphisms (a b : ℤ) :
    (fixedAcyclicBounds P a b).IsClosedUnderIsomorphisms where
  of_iso e hK i hi := (hK i hi).of_iso
    (((boundedAcyclic P).ι ⋙ eval A (ComplexShape.up ℤ) i).mapIso e).symm

/-- Restricted actual truncation has a genuine zero-functor endpoint below the lower bound. -/
def fixedBoundsTruncLEZeroIso (a b n : ℤ) (hn : n < a) :
    (fixedAcyclicBounds P a b).ι ⋙ boundedAcyclicTruncLEFunctor P n ≅
      (Functor.const (fixedAcyclicBounds P a b).FullSubcategory).obj
        (0 : (boundedAcyclic P).FullSubcategory) :=
  NatIso.ofComponents (fun K ↦ by
    have hz : IsZero (((boundedAcyclicTruncLEFunctor P n).obj K.obj).obj) :=
      truncLE_isZero_below_bound K.obj.obj a b n K.property hn
    exact (boundedAcyclic P).isoMk
      (hz.iso ((boundedAcyclic P).ι.map_isZero (isZero_zero _)))) (by
        intro K L f
        apply ObjectProperty.hom_ext
        exact (truncLE_isZero_below_bound K.obj.obj a b n K.property hn).eq_of_src _ _)

/-- At the upper bound, restricted truncation is naturally the original inclusion. -/
def fixedBoundsTruncLEIdentityIso (a b n : ℤ) (hn : b ≤ n) :
    (fixedAcyclicBounds P a b).ι ⋙ boundedAcyclicTruncLEFunctor P n ≅
      (fixedAcyclicBounds P a b).ι :=
  NatIso.ofComponents (fun K ↦ by
    let := truncLE_inclusion_isIso_above_bound K.obj.obj a b n K.property hn
    exact (boundedAcyclic P).isoMk (asIso (K.obj.obj.ιTruncLE n))) (by
      intro K L f
      apply ObjectProperty.hom_ext
      exact CochainComplex.ιTruncLE_naturality f.hom.hom n)

/-- The upper endpoint forward map is exactly the original actual inclusion. -/
@[simp]
theorem fixedBoundsTruncLEIdentityIso_hom (a b n : ℤ) (hn : b ≤ n)
    (K : (fixedAcyclicBounds P a b).FullSubcategory) :
    (((fixedBoundsTruncLEIdentityIso P a b n hn).hom.app K).hom) = K.obj.obj.ιTruncLE n := rfl

variable [(abelianExactStructure A).IsExtensionClosed P]

instance fixedAcyclicBounds_extensionClosed (a b : ℤ) :
    (boundedAcyclicExactStructure P).IsExtensionClosed (fixedAcyclicBounds P a b) where
  prop_middle {S} hS h₁ h₃ i hi := by
    have hsi := (shortExact_iff_degreewise_shortExact (S.map (boundedAcyclic P).ι)).1 hS i
    exact hsi.exact.isZero_X₂ ((h₁ i hi).eq_of_src _ _) ((h₃ i hi).eq_of_tgt _ _)

instance fixedAcyclicBounds_closedUnderFiniteProducts (a b : ℤ) :
    (fixedAcyclicBounds P a b).IsClosedUnderFiniteProducts :=
  (boundedAcyclicExactStructure P).extensionClosed_finiteProducts (fixedAcyclicBounds P a b)

/-- The genuine inherited exact structure on a specified bounded acyclic stratum. -/
def fixedAcyclicExactStructure (a b : ℤ) :=
  ExactSubcategory.exactStructure (boundedAcyclicExactStructure P) (fixedAcyclicBounds P a b)

/-- Fixed-bound inclusion is a genuine exact functor. -/
def fixedAcyclicInclusionExactFunctor (a b : ℤ) :
    ExactFunctor (fixedAcyclicExactStructure P a b) (boundedAcyclicExactStructure P) :=
  ExactSubcategory.exactInclusion (boundedAcyclicExactStructure P) (fixedAcyclicBounds P a b)

/-- Every actual truncation restricted to this stratum is genuinely exact. -/
def fixedAcyclicTruncLEExactFunctor (a b n : ℤ) :
    ExactFunctor (fixedAcyclicExactStructure P a b) (boundedAcyclicExactStructure P) :=
  (fixedAcyclicInclusionExactFunctor P a b).comp (boundedAcyclicTruncLEExactFunctor P n)

end CochainComplex
