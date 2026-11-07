/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.Waldhausen.GilletWaldhausen.BoundedTermsSSetColimit
public import Colib.KTheory.Waldhausen.Functoriality
public import Colib.KTheory.Waldhausen.ZeroFunctor
public import Colib.CategoryTheory.ExactCategory.Functor.Waldhausen

/-! # Strict original-zero models for bounded term strata

The raw filtered S-diagram uses inverse-image weak maps. Each stage is given
exactly that weak class and the tagged ambient chosen zero. Thus original
inclusions and transitions are strictly based. Exact identity functors link
these models to the original inherited isomorphism models; no comparison
or universe-change equivalence is assumed.


Implementation provenance:
`Quillen/Waldhausen/GilletWaldhausen/BoundedTermsBasedStrata.lean` at Quillen commit
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
def boundedTermsStratumZero (N : ℕ) : (boundedTermsStratum P N).FullSubcategory :=
  ⟨(ofExactCategory (boundedTermsExactStructure P)).zero, fun i _ ↦
    (HomologicalComplex.eval A (ComplexShape.up ℤ) i).map_isZero
      ((boundedTerms P).ι.map_isZero (ofExactCategory (boundedTermsExactStructure P)).isZero)⟩

/-- This tagged object is genuinely zero in the full subcategory. -/
theorem boundedTermsStratumIsZero (N : ℕ) : IsZero (boundedTermsStratumZero P N) := by
  apply IsZero.of_full_of_faithful_of_isZero (boundedTermsStratum P N).ι
  exact (ofExactCategory (boundedTermsExactStructure P)).isZero

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [(abelianExactStructure A).IsExtensionClosed P] in
/-- Actual inverse-image weak maps coincide propositionally with stage isomorphisms. -/
theorem boundedTermsStratumWeak_iso (N : ℕ) :
    boundedTermsStratumWeak P (MorphismProperty.isomorphisms _) N =
      MorphismProperty.isomorphisms _ := by
  ext X Y f
  exact ObjectProperty.isIso_hom_iff f

/-- A genuine stage Waldhausen structure with the strict ambient chosen zero. -/
def boundedTermsBasedStructure (N : ℕ) : Structure (boundedTermsStratum P N).FullSubcategory :=
  { ofExactCategory (boundedTermsStratumExactStructure P N) with
    zero := boundedTermsStratumZero P N
    isZero := boundedTermsStratumIsZero P N
    weq := boundedTermsStratumWeak P (MorphismProperty.isomorphisms _) N
    weq_multiplicative := inferInstance
    weq_iso := by rw [boundedTermsStratumWeak_iso]
    cof_zero := fun X ↦ by
      apply (boundedTermsStratum_inflation_iff P N _).2
      have he : ((boundedTermsStratumIsZero P N).to_ X).hom =
          (ofExactCategory (boundedTermsExactStructure P)).isZero.to_ X.obj :=
        (ofExactCategory (boundedTermsExactStructure P)).isZero.eq_of_src _ _
      rw [he]
      exact (ofExactCategory (boundedTermsExactStructure P)).cof_zero X.obj
    gluing := by
      rw [boundedTermsStratumWeak_iso]
      exact (ofExactCategory (boundedTermsStratumExactStructure P N)).gluing }

/-- The original stage inclusion is exact for this raw-diagram model. -/
theorem boundedTermsBasedInclusionExact (N : ℕ) :
    IsExact (boundedTermsBasedStructure P N).cof (boundedTermsBasedStructure P N).weq
      (ofExactCategory (boundedTermsExactStructure P)).cof
      (ofExactCategory (boundedTermsExactStructure P)).weq (boundedTermsStratum P N).ι :=
  boundedTermsStratumInclusion_isExact P (MorphismProperty.isomorphisms _) N

/-- The original increasing transition is exact for the same chosen-zero models. -/
theorem boundedTermsBasedTransitionExact {N M : ℕ} (h : N ≤ M) :
    IsExact (boundedTermsBasedStructure P N).cof (boundedTermsBasedStructure P N).weq
      (boundedTermsBasedStructure P M).cof (boundedTermsBasedStructure P M).weq
      (boundedTermsStratumTransition P h) :=
  boundedTermsStratumTransition_isExact P (MorphismProperty.isomorphisms _) h

/-- The actual original inclusion is strictly based, without rebasing its functor. -/
theorem boundedTermsBasedInclusion_zero (N : ℕ) :
    (boundedTermsStratum P N).ι.obj (boundedTermsBasedStructure P N).zero =
      (ofExactCategory (boundedTermsExactStructure P)).zero := rfl

/-- The original transitions retain these tagged chosen zeros exactly. -/
theorem boundedTermsBasedTransition_zero {N M : ℕ} (h : N ≤ M) :
    (boundedTermsStratumTransition P h).obj (boundedTermsBasedStructure P N).zero =
      (boundedTermsBasedStructure P M).zero := rfl

/-- The identity to the original inherited model is genuinely exact. -/
theorem boundedTermsBasedToOriginalExact (N : ℕ) :
    IsExact (boundedTermsBasedStructure P N).cof (boundedTermsBasedStructure P N).weq
      (ofExactCategory (boundedTermsStratumExactStructure P N)).cof
      (ofExactCategory (boundedTermsStratumExactStructure P N)).weq (𝟭 _) where
  zero h := h
  cofibration _ h := h
  weak f h := (ObjectProperty.isIso_hom_iff f).1 h
  pushout _ h := h

/-- The reverse original identity is genuinely exact as well. -/
theorem boundedTermsOriginalToBasedExact (N : ℕ) :
    IsExact (ofExactCategory (boundedTermsStratumExactStructure P N)).cof
      (ofExactCategory (boundedTermsStratumExactStructure P N)).weq
      (boundedTermsBasedStructure P N).cof (boundedTermsBasedStructure P N).weq (𝟭 _) where
  zero h := h
  cofibration _ h := h
  weak f h := (ObjectProperty.isIso_hom_iff f).2 h
  pushout _ h := h

/-- Original canonical K-maps of the two identity functors are inverse. -/
theorem boundedTermsOriginalBased_KMap_inv (N k : ℕ)
    (x : (ofExactCategory (boundedTermsStratumExactStructure P N)).K k) :
    KMap (boundedTermsBasedToOriginalExact P N) k
      (KMap (boundedTermsOriginalToBasedExact P N) k x) = x := by
  have h := DFunLike.congr_fun (KMap_comp_KMap (boundedTermsOriginalToBasedExact P N)
    (boundedTermsBasedToOriginalExact P N) k).symm x
  simpa only [KMap_id, MonoidHom.id_apply, MonoidHom.comp_apply] using h.symm

/-- Composing the exact identity with the original inclusion retains its canonical K-map. -/
theorem boundedTermsBasedInclusion_KMap (N k : ℕ)
    (x : (boundedTermsBasedStructure P N).K k) :
    KMap (fixedTermsInclusionExactFunctor P (-(N : ℤ)) N).waldhausenExact k
      (KMap (boundedTermsBasedToOriginalExact P N) k x) =
        KMap (boundedTermsBasedInclusionExact P N) k x :=
  (DFunLike.congr_fun (KMap_comp_KMap (boundedTermsBasedToOriginalExact P N)
    (fixedTermsInclusionExactFunctor P (-(N : ℤ)) N).waldhausenExact k).symm x).symm

/-- Transporting an original class before inclusion does not change its image. -/
theorem boundedTermsOriginalInclusion_KMap (N k : ℕ)
    (x : (ofExactCategory (boundedTermsStratumExactStructure P N)).K k) :
    KMap (boundedTermsBasedInclusionExact P N) k
      (KMap (boundedTermsOriginalToBasedExact P N) k x) =
        KMap (fixedTermsInclusionExactFunctor P (-(N : ℤ)) N).waldhausenExact k x := by
  rw [← boundedTermsBasedInclusion_KMap, boundedTermsOriginalBased_KMap_inv]

/-- The canonical transition maps commute with the original exact identity maps. -/
theorem boundedTermsBasedTransition_KMap {N M : ℕ} (h : N ≤ M) (k : ℕ)
    (x : (boundedTermsBasedStructure P N).K k) :
    KMap (boundedTermsStratumTransitionExact P h).waldhausenExact k
      (KMap (boundedTermsBasedToOriginalExact P N) k x) =
        KMap (boundedTermsBasedToOriginalExact P M) k
          (KMap (boundedTermsBasedTransitionExact P h) k x) := by
  have h₁ := DFunLike.congr_fun (KMap_comp_KMap (boundedTermsBasedToOriginalExact P N)
    (boundedTermsStratumTransitionExact P h).waldhausenExact k).symm x
  have h₂ := DFunLike.congr_fun (KMap_comp_KMap (boundedTermsBasedTransitionExact P h)
    (boundedTermsBasedToOriginalExact P M) k).symm x
  exact h₁.symm.trans h₂

end CategoryTheory.Waldhausen.GilletWaldhausen
