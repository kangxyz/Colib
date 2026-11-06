/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Pullbacks
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.IdentityDisk
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.QuotientExact

/-! # The actual one-step acyclic truncation layer is a two-term disk

The layer is the existing actual quotient of truncLE (n+1) by its
truncLE n. Its natural identification with the identity disk on the actual
(n+1)-st cycles is constructed using the original quotient projection and
boundary-cycle isomorphism. All maps are actual chain maps.
-/
/-! Adapted from
`Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.TruncationLayer`
at pinned Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe v u
namespace CochainComplex

attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The only differential of an acyclic two-term complex is invertible. -/
theorem twoTermDifferential_isIso (K : CochainComplex A ℤ) (n : ℤ) (hK : K.Acyclic)
    (hz : ∀ i, i ≠ n → i ≠ n + 1 → IsZero (K.X i)) : IsIso (K.d n (n + 1)) := by
  let : Mono (K.d n (n + 1)) :=
    (ShortComplex.exact_iff_mono (K.sc' (n - 1) n (n + 1))
      ((hz (n - 1) (by omega) (by omega)).eq_of_src _ _)).1
        ((K.exactAt_iff' (n - 1) n (n + 1) (by simp) (by simp)).1 (hK n))
  let : Epi (K.d n (n + 1)) :=
    (ShortComplex.exact_iff_epi (K.sc' n (n + 1) (n + 2))
      ((hz (n + 2) (by omega) (by omega)).eq_of_tgt _ _)).1
        ((K.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp; omega)).1 (hK (n + 1)))
  exact isIso_of_mono_of_epi _

/-- Into a complex whose differential is mono, a map from the identity disk
is determined by its upper component. -/
theorem identityDisk_hom_ext_top (n : ℤ) {X : A} {K : CochainComplex A ℤ}
    [Mono (K.d n (n + 1))] (f g : identityDisk n X ⟶ K)
    (h : f.f (n + 1) = g.f (n + 1)) : f = g := by
  apply from_double_hom_ext
  · apply (cancel_mono (K.d n (n + 1))).1
    rw [f.comm, g.comm, h]
  · exact h

variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsKernelClosed P]

/-- The actual one-step layer, with its actual induced cokernel maps. -/
def oneStepLayerFunctor (n : ℤ) :
    (boundedAcyclic P).FullSubcategory ⥤ (boundedAcyclic P).FullSubcategory :=
  boundedAcyclicTruncLEFunctor P (n + 1) ⋙ boundedAcyclicQuotientFunctor P n

/-- The genuine layer is concentrated in exactly the two allowed degrees. -/
theorem oneStepLayer_isZero (n : ℤ) (K : (boundedAcyclic P).FullSubcategory)
    (i : ℤ) (h₀ : i ≠ n) (h₁ : i ≠ n + 1) :
    IsZero (((oneStepLayerFunctor P n).obj K).obj.X i) := by
  by_cases hi : i < n
  · exact truncationQuotient_isZero_below (K.obj.truncLE (n + 1)) n i hi
  · exact IsZero.of_epi (((K.obj.truncLE (n + 1)).shortComplexTruncLE n).g.f i)
      ((K.obj.truncLE (n + 1)).isZero_of_isStrictlyLE (n + 1) i (by omega))

/-- Its sole differential is invertible because the actual layer is acyclic. -/
theorem oneStepLayer_d_isIso (n : ℤ) (K : (boundedAcyclic P).FullSubcategory) :
    IsIso (((oneStepLayerFunctor P n).obj K).obj.d n (n + 1)) :=
  twoTermDifferential_isIso _ n ((oneStepLayerFunctor P n).obj K).property.2.2
    (oneStepLayer_isZero P n K)

/-- The layer's upper term identifies with the original actual cycles. -/
def oneStepLayerTopIso (n : ℤ) (K : (boundedAcyclic P).FullSubcategory) :
    ((oneStepLayerFunctor P n).obj K).obj.X (n + 1) ≅ K.obj.cycles (n + 1) := by
  let := isIso_truncationQuotient_projection_above (K.obj.truncLE (n + 1)) n (n + 1) (by omega)
  exact (asIso (((K.obj.truncLE (n + 1)).shortComplexTruncLE n).g.f (n + 1))).symm ≪≫
    K.obj.truncLEXIsoCycles (n + 1)

/-- This identification is natural for the original induced quotient maps. -/
@[reassoc]
theorem oneStepLayerTopIso_naturality (n : ℤ)
    {K L : (boundedAcyclic P).FullSubcategory} (f : K ⟶ L) :
    ((oneStepLayerFunctor P n).map f).hom.f (n + 1) ≫ (oneStepLayerTopIso P n L).hom =
      (oneStepLayerTopIso P n K).hom ≫ cyclesMap f.hom (n + 1) := by
  apply (cancel_epi (((K.obj.truncLE (n + 1)).shortComplexTruncLE n).g.f (n + 1))).1
  have h := congrArg (fun g ↦ g.f (n + 1))
    (truncationQuotient_naturality (CochainComplex.truncLEMap f.hom (n + 1)) n)
  change (((K.obj.truncLE (n + 1)).shortComplexTruncLE n).g.f (n + 1)) ≫
    ((oneStepLayerFunctor P n).map f).hom.f (n + 1) =
      (CochainComplex.truncLEMap f.hom (n + 1)).f (n + 1) ≫
        (((L.obj.truncLE (n + 1)).shortComplexTruncLE n).g.f (n + 1)) at h
  dsimp only [oneStepLayerTopIso, Iso.trans_hom, Iso.symm_hom, asIso_inv]
  rw [← Category.assoc, h]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  exact (truncLEEvalIsoCycles (A := A) (n + 1)).hom.naturality f.hom

/-- The natural upper-term identification of the actual layer functor. -/
def oneStepLayerEvalIsoCycles (n : ℤ) :
    oneStepLayerFunctor P n ⋙ (boundedAcyclic P).ι ⋙ eval A (ComplexShape.up ℤ) (n + 1) ≅
      boundedAcyclicCyclesFunctor P (n + 1) ⋙ P.ι :=
  NatIso.ofComponents (oneStepLayerTopIso P n) (oneStepLayerTopIso_naturality P n)

/-- The canonical chain map from the actual identity disk to the actual layer. -/
def identityDiskToOneStepLayer (n : ℤ) (K : (boundedAcyclic P).FullSubcategory) :
    identityDisk n (K.obj.cycles (n + 1)) ⟶ ((oneStepLayerFunctor P n).obj K).obj := by
  let := oneStepLayer_d_isIso P n K
  exact mkHomFromDouble (show (ComplexShape.up ℤ).Rel n (n + 1) by simp) (by omega)
    ((oneStepLayerTopIso P n K).inv ≫ inv (((oneStepLayerFunctor P n).obj K).obj.d n (n + 1)))
    (oneStepLayerTopIso P n K).inv (by simp) (by
      intro i hi
      have hi' : n + 1 + 1 = i := hi
      have hz := oneStepLayer_isZero P n K i (by omega) (by omega)
      rw [hz.eq_of_tgt (((oneStepLayerFunctor P n).obj K).obj.d (n + 1) i) 0, comp_zero])

@[simp]
theorem identityDiskToOneStepLayer_f₁ (n : ℤ) (K : (boundedAcyclic P).FullSubcategory) :
    (identityDiskToOneStepLayer P n K).f (n + 1) =
      (identityDiskIso₁ n (K.obj.cycles (n + 1))).hom ≫ (oneStepLayerTopIso P n K).inv := by
  simp [identityDiskToOneStepLayer, identityDiskIso₁]

/-- The canonical layer map is an actual isomorphism in every degree. -/
theorem identityDiskToOneStepLayer_isIso (n : ℤ) (K : (boundedAcyclic P).FullSubcategory) :
    IsIso (identityDiskToOneStepLayer P n K) := by
  let := oneStepLayer_d_isIso P n K
  let (i : ℤ) : IsIso ((identityDiskToOneStepLayer P n K).f i) := by
    by_cases h₀ : i = n
    · subst i
      simp only [identityDiskToOneStepLayer, mkHomFromDouble_f₀]
      infer_instance
    · by_cases h₁ : i = n + 1
      · subst i
        rw [identityDiskToOneStepLayer_f₁]
        infer_instance
      · exact (identityDisk_isZero n (K.obj.cycles (n + 1)) i h₀ h₁).isIso
          (oneStepLayer_isZero P n K i h₀ h₁) _
  exact Hom.isIso_of_components _

/-- The natural actual disk-to-layer isomorphism in the inherited full category. -/
def diskToOneStepLayerIso (n : ℤ) :
    boundedAcyclicCyclesFunctor P (n + 1) ⋙ boundedAcyclicDiskFunctor P n ≅
      oneStepLayerFunctor P n :=
  NatIso.ofComponents (fun K ↦ by
    let := identityDiskToOneStepLayer_isIso P n K
    exact (boundedAcyclic P).isoMk (asIso (identityDiskToOneStepLayer P n K))) (by
      intro K L f
      apply ObjectProperty.hom_ext
      let := oneStepLayer_d_isIso P n L
      apply identityDisk_hom_ext_top n
      change (identityDiskMap n (cyclesMap f.hom (n + 1))).f (n + 1) ≫
          (identityDiskToOneStepLayer P n L).f (n + 1) =
        (identityDiskToOneStepLayer P n K).f (n + 1) ≫
          ((oneStepLayerFunctor P n).map f).hom.f (n + 1)
      rw [identityDiskMap_f₁, identityDiskToOneStepLayer_f₁, identityDiskToOneStepLayer_f₁]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      apply congrArg ((identityDiskIso₁ n (K.obj.cycles (n + 1))).hom ≫ ·)
      exact (oneStepLayerEvalIsoCycles P n).inv.naturality f)

/-- The actual one-step truncation quotient is naturally the two-term identity
 disk on the original next-cycle functor. -/
def oneStepLayerDiskIso (n : ℤ) :
    oneStepLayerFunctor P n ≅
      boundedAcyclicCyclesFunctor P (n + 1) ⋙ boundedAcyclicDiskFunctor P n :=
  (diskToOneStepLayerIso P n).symm

variable [(abelianExactStructure A).IsExtensionClosed P]

local instance : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P

/-- The actual layer is a genuine exact functor, by the two established
exact truncation and quotient functors. -/
def oneStepLayerExactFunctor (n : ℤ) :
    ExactFunctor (boundedAcyclicExactStructure P) (boundedAcyclicExactStructure P) :=
  (boundedAcyclicTruncLEExactFunctor P (n + 1)).comp (boundedAcyclicQuotientExactFunctor P n)

@[simp]
theorem oneStepLayerExactFunctor_toFunctor (n : ℤ) :
    (oneStepLayerExactFunctor P n).toFunctor = oneStepLayerFunctor P n := rfl

/-- The actual cycle-disk composite is likewise a genuine exact functor. -/
def oneStepCycleDiskExactFunctor (n : ℤ) :
    ExactFunctor (boundedAcyclicExactStructure P) (boundedAcyclicExactStructure P) :=
  (boundedAcyclicCyclesExactFunctor P (n + 1)).comp (boundedAcyclicDiskExactFunctor P n)

@[simp]
theorem oneStepCycleDiskExactFunctor_toFunctor (n : ℤ) :
    (oneStepCycleDiskExactFunctor P n).toFunctor =
      boundedAcyclicCyclesFunctor P (n + 1) ⋙ boundedAcyclicDiskFunctor P n := rfl

end CochainComplex
