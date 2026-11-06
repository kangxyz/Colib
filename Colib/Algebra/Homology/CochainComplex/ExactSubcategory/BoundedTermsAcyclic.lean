/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Pullbacks
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.BoundedTerms

/-! # The actual acyclic subcategory of bounded termwise-P complexes

The original bounded acyclic category includes exactly into the new ambient
bounded category, and its inherited cofibrations are precisely the ambient
inherited cofibrations between its objects. The genuine quasi-isomorphism
condition from an actual zero object is characterized by actual acyclicity.
No fibration theorem or K-equivalence is assumed.
-/
/-! Adapted from
`Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.BoundedTermsAcyclic`
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
variable (P : ObjectProperty A)

/-- Forgetting acyclicity leaves the original bounded termwise conditions. -/
theorem boundedAcyclic_le_boundedTerms : boundedAcyclic P ≤ boundedTerms P :=
  fun _ hK ↦ ⟨hK.1, hK.2.1⟩

/-- The actual full-subcategory inclusion, with unchanged complexes and chain maps. -/
def boundedAcyclicTermsInclusion :
    (boundedAcyclic P).FullSubcategory ⥤ (boundedTerms P).FullSubcategory :=
  ObjectProperty.ιOfLE (boundedAcyclic_le_boundedTerms P)

@[simp]
theorem boundedAcyclicTermsInclusion_comp_ι :
    boundedAcyclicTermsInclusion P ⋙ (boundedTerms P).ι = (boundedAcyclic P).ι := rfl

instance boundedAcyclicTermsInclusion_additive : (boundedAcyclicTermsInclusion P).Additive where
  map_add := by intros; rfl

variable [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]

/-- Exactness of the original inclusion for the actual inherited conflations. -/
def boundedAcyclicTermsExactInclusion :
    ExactFunctor (boundedAcyclicExactStructure P) (boundedTermsExactStructure P) where
  toFunctor := boundedAcyclicTermsInclusion P
  map_conflation _ hS := hS

/-- Between acyclic objects, an inherited ambient quotient is automatically
acyclic, so the actual inclusion reflects inherited inflations. -/
theorem boundedAcyclicTermsInclusion_inflation_iff
    {K L : (boundedAcyclic P).FullSubcategory} (f : K ⟶ L) :
    (boundedTermsExactStructure P).inflation ((boundedAcyclicTermsInclusion P).map f) ↔
      (boundedAcyclicExactStructure P).inflation f := by
  constructor
  · intro hf
    obtain ⟨Q, p, w, hS⟩ := hf
    let S := (ShortComplex.mk ((boundedAcyclicTermsInclusion P).map f) p w).map (boundedTerms P).ι
    have hs : S.ShortExact := hS
    have hq : QuasiIso S.f := by
      rw [quasiIso_iff]
      intro n
      exact (quasiIsoAt_iff_exactAt' f.hom n (L.property.2.2 n)).2 (K.property.2.2 n)
    apply (ExactSubcategory.inflation_iff (abelianExactStructure (CochainComplex A ℤ))
      (boundedAcyclic P) f).2
    exact ⟨Q.obj, ⟨Q.property.1, Q.property.2, hs.acyclic_X₃ hq⟩,
      p.hom, congrArg (fun z ↦ z.hom) w, hS⟩
  · exact (boundedAcyclicTermsExactInclusion P).map_inflation f

end CochainComplex
