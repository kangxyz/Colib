/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Pullbacks
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.FiniteCycleBounds
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.AdjacentTruncation

/-!
# Actual smart-truncation filtrations within a fixed term interval

The original truncations, cycle disks and their natural inclusion/projection
maps stay in the specified acyclic term stratum. Their actual layer sequence is
an inherited conflation; its lower endpoint is zero and upper endpoint identity.
-/
/-! Adapted from
`Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.FiniteCycleFiltration`
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
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsKernelClosed P]

/-- The original smart truncation stays in the specified acyclic term stratum. -/
def finiteCycleTruncation (a b n : ℤ) :
    (fixedAcyclicBounds P a b).FullSubcategory ⥤ (fixedAcyclicBounds P a b).FullSubcategory :=
  (fixedAcyclicBounds P a b).lift
    ((fixedAcyclicBounds P a b).ι ⋙ boundedAcyclicTruncLEFunctor P n)
    (fun K ↦ K.property.truncLE n)

instance finiteCycleTruncation_additive (a b n : ℤ) : (finiteCycleTruncation P a b n).Additive :=
  inferInstanceAs (Functor.Additive ((fixedAcyclicBounds P a b).lift _ _))

/-- The actual smart inclusion is naturally invertible at and beyond the upper bound. -/
def finiteCycleIdentityIso (a b n : ℤ) (hn : b ≤ n) :
    finiteCycleTruncation P a b n ≅ 𝟭 (fixedAcyclicBounds P a b).FullSubcategory :=
  NatIso.ofComponents (fun K ↦ (fixedAcyclicBounds P a b).isoMk
    ((fixedBoundsTruncLEIdentityIso P a b n hn).app K)) (by
      intro K L f
      exact ObjectProperty.hom_ext _
        ((fixedBoundsTruncLEIdentityIso P a b n hn).hom.naturality f))

@[simp] theorem finiteCycleIdentityIso_hom (a b n : ℤ) (hn : b ≤ n)
    (K : (fixedAcyclicBounds P a b).FullSubcategory) :
    (((finiteCycleIdentityIso P a b n hn).hom.app K).hom.hom) = K.obj.obj.ιTruncLE n := rfl

/-- Acyclicity makes the lower-bound smart truncation actually zero in the same stratum. -/
theorem finiteCycleTruncation_isZero (a b : ℤ)
    (K : (fixedAcyclicBounds P a b).FullSubcategory) : IsZero ((finiteCycleTruncation P a b
      a).obj K) := by
  apply IsZero.of_full_of_faithful_of_isZero (fixedAcyclicBounds P a b).ι
  apply IsZero.of_full_of_faithful_of_isZero (boundedAcyclic P).ι
  exact truncLE_isZero_at_lower_bound K.obj.obj a b K.property K.obj.property.2.2

/-- The original lower endpoint is naturally the actual zero functor. -/
def finiteCycleZeroIso (a b : ℤ) :
    finiteCycleTruncation P a b a ≅
      (Functor.const (fixedAcyclicBounds P a b).FullSubcategory).obj
        (0 : (fixedAcyclicBounds P a b).FullSubcategory) :=
  NatIso.ofComponents (fun K ↦ (finiteCycleTruncation_isZero P a b K).iso (isZero_zero _)) (by
    intro K L f
    exact (finiteCycleTruncation_isZero P a b K).eq_of_src _ _)

variable [(abelianExactStructure A).IsExtensionClosed P]

/-- The original disk quotient retains the target's actual bounds by its genuine epi. -/
theorem finiteCycleLayer_hasTermBounds (a b n : ℤ) (K : (boundedAcyclic P).FullSubcategory)
    (hK : HasTermBounds K.obj a b) : HasTermBounds (identityDisk n (K.obj.cycles (n + 1))) a b := by
  let S := ShortComplex.mk ((adjacentTruncationInclusion P n).app K)
    ((adjacentTruncationProjection P n).app K)
    (NatTrans.congr_app (adjacentTruncation_comp_zero P n) K)
  have hS := adjacentTruncation_conflation P n K
  intro i hi
  have hs := (shortExact_iff_degreewise_shortExact (S.map (boundedAcyclic P).ι)).1 hS i
  let : Epi (((adjacentTruncationProjection P n).app K).hom.f i) := hs.epi_g
  exact IsZero.of_epi (((adjacentTruncationProjection P n).app K).hom.f i)
    (hK.truncLE (n + 1) i hi)

/-- The actual disk on the next cycles is an endofunctor of the same stratum. -/
def finiteCycleLayer (a b n : ℤ) :
    (fixedAcyclicBounds P a b).FullSubcategory ⥤ (fixedAcyclicBounds P a b).FullSubcategory :=
  (fixedAcyclicBounds P a b).lift
    ((fixedAcyclicBounds P a b).ι ⋙ boundedAcyclicCyclesFunctor P (n + 1) ⋙
      boundedAcyclicDiskFunctor P n)
    (fun K ↦ finiteCycleLayer_hasTermBounds P a b n K.obj K.property)

instance finiteCycleLayer_additive (a b n : ℤ) : (finiteCycleLayer P a b n).Additive :=
  inferInstanceAs (Functor.Additive ((fixedAcyclicBounds P a b).lift _ _))

/-- The actual adjacent inclusion is retained without replacing its original chain map. -/
def finiteCycleInclusion (a b n : ℤ) :
    finiteCycleTruncation P a b n ⟶ finiteCycleTruncation P a b (n + 1) where
  app K := (fixedAcyclicBounds P a b).homMk ((adjacentTruncationInclusion P n).app K.obj)
  naturality _ _ f := ObjectProperty.hom_ext _ ((adjacentTruncationInclusion P n).naturality f.hom)

/-- The original quotient projection followed by its actual disk identification. -/
def finiteCycleProjection (a b n : ℤ) :
    finiteCycleTruncation P a b (n + 1) ⟶ finiteCycleLayer P a b n where
  app K := (fixedAcyclicBounds P a b).homMk ((adjacentTruncationProjection P n).app K.obj)
  naturality _ _ f := ObjectProperty.hom_ext _ ((adjacentTruncationProjection P n).naturality f.hom)

@[reassoc] theorem finiteCycle_comp_zero (a b n : ℤ) :
    finiteCycleInclusion P a b n ≫ finiteCycleProjection P a b n = 0 := by
  apply NatTrans.ext
  funext K
  exact ObjectProperty.hom_ext _ (NatTrans.congr_app (adjacentTruncation_comp_zero P n) K.obj)

/-- Exactness of the original restricted smart endofunctor. -/
def finiteCycleTruncationExact (a b n : ℤ) :
    ExactFunctor (fixedAcyclicExactStructure P a b) (fixedAcyclicExactStructure P a b) where
  toFunctor := finiteCycleTruncation P a b n
  map_conflation S hS := (boundedAcyclicTruncLEExactFunctor P n).map_conflation
    (S.map (fixedAcyclicBounds P a b).ι) hS

/-- Exactness of the original disk-cycle quotient endofunctor. -/
def finiteCycleLayerExact (a b n : ℤ) :
    ExactFunctor (fixedAcyclicExactStructure P a b) (fixedAcyclicExactStructure P a b) where
  toFunctor := finiteCycleLayer P a b n
  map_conflation S hS := (oneStepCycleDiskExactFunctor P n).map_conflation
    (S.map (fixedAcyclicBounds P a b).ι) hS

/-- The pointwise sequence is the original actual adjacent conflation. -/
theorem finiteCycleLayer_conflation (a b n : ℤ) (K : (fixedAcyclicBounds P a b).FullSubcategory) :
    (fixedAcyclicExactStructure P a b).conflation
      (ShortComplex.mk ((finiteCycleInclusion P a b n).app K) ((finiteCycleProjection P a b
        n).app K)
        (NatTrans.congr_app (finiteCycle_comp_zero P a b n) K)) :=
  adjacentTruncation_conflation P n K.obj

end CochainComplex
