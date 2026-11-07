/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.ComplexSubcategory

public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.BoundedTermsAcyclic
public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Pullbacks
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.BoundedTerms
public import Colib.CategoryTheory.ExactCategory.Functor.Waldhausen

/-! # The actual acyclic subcategory of bounded termwise-P complexes

The original bounded acyclic category includes exactly into the new ambient
bounded category, and its inherited cofibrations are precisely the ambient
inherited cofibrations between its objects. The genuine quasi-isomorphism
condition from an actual zero object is characterized by actual acyclicity.
No fibration theorem or K-equivalence is assumed.


Implementation provenance:
`Quillen/Waldhausen/GilletWaldhausen/BoundedTermsAcyclic.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps, bounds, hypotheses
and independent object/hom universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.ExactCategory
open CochainComplex

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe v u
namespace CategoryTheory.Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A)

variable [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]

/-- The same original inclusion is exact with genuine quasi-isomorphisms. -/
theorem boundedAcyclicTermsInclusion_quasiExact :
    IsExact (complexSubcategory (boundedAcyclic P)).cof (complexSubcategory (boundedAcyclic P)).weq
      (complexSubcategory (boundedTerms P)).cof (complexSubcategory (boundedTerms P)).weq
      (boundedAcyclicTermsInclusion P) where
  zero h := (boundedAcyclicTermsInclusion P).map_isZero h
  cofibration f hf := (boundedAcyclicTermsExactInclusion P).map_inflation f hf
  weak _ hf := hf
  pushout hi h := (boundedAcyclicTermsExactInclusion P).map_isPushout hi h

/-- Any map from any actual zero object is a genuine quasi-isomorphism
precisely when its target is actually acyclic. -/
theorem boundedTerms_weq_from_zero_iff
    {Z K : (boundedTerms P).FullSubcategory} (hZ : IsZero Z) (f : Z ⟶ K) :
    (complexSubcategory (boundedTerms P)).weq f ↔ K.obj.Acyclic := by
  have hz := acyclic_of_isZero Z.obj ((boundedTerms P).ι.map_isZero hZ)
  change QuasiIso f.hom ↔ K.obj.Acyclic
  rw [quasiIso_iff]
  exact forall_congr' (fun n ↦ quasiIsoAt_iff_exactAt f.hom n (hz n))

/-- The standard Waldhausen weakly-acyclic predicate is exactly actual
acyclicity of the original bounded complex. -/
theorem boundedTerms_weaklyAcyclic_iff (K : (boundedTerms P).FullSubcategory) :
    (complexSubcategory (boundedTerms P)).weq
      ((complexSubcategory (boundedTerms P)).isZero.to_ K) ↔ boundedAcyclic P K.obj := by
  rw [boundedTerms_weq_from_zero_iff P (complexSubcategory (boundedTerms P)).isZero]
  exact ⟨fun h ↦ ⟨K.property.1, K.property.2, h⟩, fun h ↦ h.2.2⟩

end CategoryTheory.Waldhausen.GilletWaldhausen
