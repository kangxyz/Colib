/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.Waldhausen.GilletWaldhausen.BoundedSSetColimit
public import Colib.KTheory.Waldhausen.Functoriality
public import Colib.KTheory.Waldhausen.ZeroFunctor
public import Colib.CategoryTheory.ExactCategory.Functor.Waldhausen

/-! # Strict original-zero models for bounded acyclic term strata

The raw filtered S-diagram uses inverse-image weak maps. Each stage is given
exactly that weak class and the tagged ambient chosen zero. Thus original
inclusions and transitions are strictly based. Exact identity functors link
these models to the original inherited isomorphism models; no comparison
or universe-change equivalence is assumed.


Implementation provenance:
`Quillen/Waldhausen/GilletWaldhausen/BoundedAcyclicBasedStrata.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps, bounds, hypotheses
and independent object/hom universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.ExactCategory
open CochainComplex


noncomputable section
open Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial ZeroObject
universe v u
namespace CategoryTheory.Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]

/-- The actual ambient chosen zero, tagged with its actual term bounds. -/
def boundedAcyclicStratumZero (N : ℕ) : (boundedStratum P N).FullSubcategory :=
  ⟨(ofExactCategory (boundedAcyclicExactStructure P)).zero, fun i _ ↦
    (HomologicalComplex.eval A (ComplexShape.up ℤ) i).map_isZero
      ((boundedAcyclic P).ι.map_isZero (ofExactCategory (boundedAcyclicExactStructure P)).isZero)⟩

/-- This tagged object is genuinely zero in the full subcategory. -/
theorem boundedAcyclicStratumIsZero (N : ℕ) : IsZero (boundedAcyclicStratumZero P N) := by
  apply IsZero.of_full_of_faithful_of_isZero (boundedStratum P N).ι
  exact (ofExactCategory (boundedAcyclicExactStructure P)).isZero

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [(abelianExactStructure A).IsExtensionClosed P] in
/-- Actual inverse-image weak maps coincide propositionally with stage isomorphisms. -/
theorem boundedAcyclicStratumWeak_iso (N : ℕ) :
    boundedStratumWeak P (MorphismProperty.isomorphisms _) N =
      MorphismProperty.isomorphisms _ := by
  ext X Y f
  exact ObjectProperty.isIso_hom_iff f

/-- A genuine stage Waldhausen structure with the strict ambient chosen zero. -/
def boundedAcyclicBasedStructure (N : ℕ) : Structure (boundedStratum P N).FullSubcategory :=
  { ofExactCategory (boundedStratumExactStructure P N) with
    zero := boundedAcyclicStratumZero P N
    isZero := boundedAcyclicStratumIsZero P N
    weq := boundedStratumWeak P (MorphismProperty.isomorphisms _) N
    weq_multiplicative := inferInstance
    weq_iso := by rw [boundedAcyclicStratumWeak_iso]
    cof_zero := fun X ↦ by
      apply (boundedStratum_inflation_iff P N _).2
      have he : ((boundedAcyclicStratumIsZero P N).to_ X).hom =
          (ofExactCategory (boundedAcyclicExactStructure P)).isZero.to_ X.obj :=
        (ofExactCategory (boundedAcyclicExactStructure P)).isZero.eq_of_src _ _
      rw [he]
      exact (ofExactCategory (boundedAcyclicExactStructure P)).cof_zero X.obj
    gluing := by
      rw [boundedAcyclicStratumWeak_iso]
      exact (ofExactCategory (boundedStratumExactStructure P N)).gluing }

/-- The original stage inclusion is exact for this raw-diagram model. -/
theorem boundedAcyclicBasedInclusionExact (N : ℕ) :
    IsExact (boundedAcyclicBasedStructure P N).cof (boundedAcyclicBasedStructure P N).weq
      (ofExactCategory (boundedAcyclicExactStructure P)).cof
      (ofExactCategory (boundedAcyclicExactStructure P)).weq (boundedStratum P N).ι :=
  boundedStratumInclusion_isExact P (MorphismProperty.isomorphisms _) N

/-- The original increasing transition is exact for the same chosen-zero models. -/
theorem boundedAcyclicBasedTransitionExact {N M : ℕ} (h : N ≤ M) :
    IsExact (boundedAcyclicBasedStructure P N).cof (boundedAcyclicBasedStructure P N).weq
      (boundedAcyclicBasedStructure P M).cof (boundedAcyclicBasedStructure P M).weq
      (boundedStratumTransition P h) :=
  boundedStratumTransition_isExact P (MorphismProperty.isomorphisms _) h

/-- The actual original inclusion is strictly based, without rebasing its functor. -/
theorem boundedAcyclicBasedInclusion_zero (N : ℕ) :
    (boundedStratum P N).ι.obj (boundedAcyclicBasedStructure P N).zero =
      (ofExactCategory (boundedAcyclicExactStructure P)).zero := rfl

/-- The original transitions retain these tagged chosen zeros exactly. -/
theorem boundedAcyclicBasedTransition_zero {N M : ℕ} (h : N ≤ M) :
    (boundedStratumTransition P h).obj (boundedAcyclicBasedStructure P N).zero =
      (boundedAcyclicBasedStructure P M).zero := rfl

/-- The identity to the original inherited model is genuinely exact. -/
theorem boundedAcyclicBasedToOriginalExact (N : ℕ) :
    IsExact (boundedAcyclicBasedStructure P N).cof (boundedAcyclicBasedStructure P N).weq
      (ofExactCategory (boundedStratumExactStructure P N)).cof
      (ofExactCategory (boundedStratumExactStructure P N)).weq (𝟭 _) where
  zero h := h
  cofibration _ h := h
  weak f h := (ObjectProperty.isIso_hom_iff f).1 h
  pushout _ h := h

/-- The reverse original identity is genuinely exact as well. -/
theorem boundedAcyclicOriginalToBasedExact (N : ℕ) :
    IsExact (ofExactCategory (boundedStratumExactStructure P N)).cof
      (ofExactCategory (boundedStratumExactStructure P N)).weq
      (boundedAcyclicBasedStructure P N).cof (boundedAcyclicBasedStructure P N).weq (𝟭 _) where
  zero h := h
  cofibration _ h := h
  weak f h := (ObjectProperty.isIso_hom_iff f).2 h
  pushout _ h := h

/-- Original canonical K-maps of the two identity functors are inverse. -/
theorem boundedAcyclicOriginalBased_KMap_inv (N k : ℕ)
    (x : (ofExactCategory (boundedStratumExactStructure P N)).K k) :
    KMap (boundedAcyclicBasedToOriginalExact P N) k
      (KMap (boundedAcyclicOriginalToBasedExact P N) k x) = x := by
  have h := DFunLike.congr_fun (KMap_comp_KMap (boundedAcyclicOriginalToBasedExact P N)
    (boundedAcyclicBasedToOriginalExact P N) k).symm x
  simpa only [KMap_id, MonoidHom.id_apply, MonoidHom.comp_apply] using h.symm

/-- Composing the exact identity with the original inclusion retains its canonical K-map. -/
theorem boundedAcyclicBasedInclusion_KMap (N k : ℕ)
    (x : (boundedAcyclicBasedStructure P N).K k) :
    KMap (fixedAcyclicInclusionExactFunctor P (-(N : ℤ)) N).waldhausenExact k
      (KMap (boundedAcyclicBasedToOriginalExact P N) k x) =
        KMap (boundedAcyclicBasedInclusionExact P N) k x :=
  (DFunLike.congr_fun (KMap_comp_KMap (boundedAcyclicBasedToOriginalExact P N)
    (fixedAcyclicInclusionExactFunctor P (-(N : ℤ)) N).waldhausenExact k).symm x).symm

/-- Transporting an original class before inclusion does not change its image. -/
theorem boundedAcyclicOriginalInclusion_KMap (N k : ℕ)
    (x : (ofExactCategory (boundedStratumExactStructure P N)).K k) :
    KMap (boundedAcyclicBasedInclusionExact P N) k
      (KMap (boundedAcyclicOriginalToBasedExact P N) k x) =
        KMap (fixedAcyclicInclusionExactFunctor P (-(N : ℤ)) N).waldhausenExact k x := by
  rw [← boundedAcyclicBasedInclusion_KMap, boundedAcyclicOriginalBased_KMap_inv]

/-- The canonical transition maps commute with the original exact identity maps. -/
theorem boundedAcyclicBasedTransition_KMap {N M : ℕ} (h : N ≤ M) (k : ℕ)
    (x : (boundedAcyclicBasedStructure P N).K k) :
    KMap (boundedStratumTransitionExact P h).waldhausenExact k
      (KMap (boundedAcyclicBasedToOriginalExact P N) k x) =
        KMap (boundedAcyclicBasedToOriginalExact P M) k
          (KMap (boundedAcyclicBasedTransitionExact P h) k x) := by
  have h₁ := DFunLike.congr_fun (KMap_comp_KMap (boundedAcyclicBasedToOriginalExact P N)
    (boundedStratumTransitionExact P h).waldhausenExact k).symm x
  have h₂ := DFunLike.congr_fun (KMap_comp_KMap (boundedAcyclicBasedTransitionExact P h)
    (boundedAcyclicBasedToOriginalExact P M) k).symm x
  exact h₁.symm.trans h₂

end CategoryTheory.Waldhausen.GilletWaldhausen
