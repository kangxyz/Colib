/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.Waldhausen.Fibration.AcyclicSubcategory
public import Colib.CategoryTheory.Waldhausen.GilletWaldhausen.BoundedTermsAcyclic

/-! # The actual nested weak models for bounded complexes

The fine model uses isomorphisms and the coarse model uses genuine
quasi-isomorphisms, with exactly the same inherited cofibrations and zero.
The actual coarse-acyclic full subcategory is identified with the original
bounded-acyclic complex category by unchanged objects and chain maps.
No fibration theorem or K-equivalence is assumed.


Implementation provenance:
`Quillen/Waldhausen/GilletWaldhausen/FibrationModels.lean` at Quillen commit
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
universe u v
namespace CategoryTheory.Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]

/-- Actual isomorphism and quasi-isomorphism weak classes share the original
inherited cofibration class and chosen zero literally. -/
def boundedTermsNested : Fibration.NestedWeakEquivalences (ofExactCategory
    (boundedTermsExactStructure P)) where
  coarse := complexSubcategory (boundedTerms P)
  cof_eq := rfl
  zero_eq := rfl
  le_weq := by
    intro X Y f hf
    let : IsIso f := hf
    change QuasiIso f.hom
    infer_instance

/-- Retain the original complex and chain maps, adding its genuine coarse-acyclic witness. -/
def boundedAcyclicToFiberObjects : (boundedAcyclic P).FullSubcategory ⥤
    Fibration.AcyclicCategory (boundedTermsNested P) where
  obj K := ⟨(boundedAcyclicTermsInclusion P).obj K,
    (boundedTerms_weaklyAcyclic_iff P _).2 K.property⟩
  map f := (Fibration.acyclicObjects (boundedTermsNested P)).homMk
    ((boundedAcyclicTermsInclusion P).map f)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The actual weak-acyclic predicate recovers genuine acyclicity of the unchanged complex. -/
def fiberObjectsToBoundedAcyclic : Fibration.AcyclicCategory (boundedTermsNested P) ⥤
    (boundedAcyclic P).FullSubcategory where
  obj K := ⟨K.obj.obj, (boundedTerms_weaklyAcyclic_iff P K.obj).1 K.property⟩
  map f := (boundedAcyclic P).homMk f.hom.hom
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem boundedAcyclicToFiberObjects_comp_inverse :
    boundedAcyclicToFiberObjects P ⋙ fiberObjectsToBoundedAcyclic P = 𝟭 _ := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

@[simp] theorem fiberObjectsToBoundedAcyclic_comp_inverse :
    fiberObjectsToBoundedAcyclic P ⋙ boundedAcyclicToFiberObjects P = 𝟭 _ := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The categorical equivalence is literal on the original complexes and maps. -/
def boundedAcyclicFiberEquivalence : (boundedAcyclic P).FullSubcategory ≌
    Fibration.AcyclicCategory (boundedTermsNested P) :=
  CategoryTheory.Equivalence.mk (boundedAcyclicToFiberObjects P) (fiberObjectsToBoundedAcyclic P)
    (eqToIso (boundedAcyclicToFiberObjects_comp_inverse P).symm)
    (eqToIso (fiberObjectsToBoundedAcyclic_comp_inverse P))

/-- Composing with the actual fiber-object inclusion gives the original bounded-acyclic
inclusion. -/
@[simp] theorem boundedAcyclicToFiberObjects_comp_inclusion :
    boundedAcyclicToFiberObjects P ⋙ Fibration.acyclicInclusion (boundedTermsNested P) =
      boundedAcyclicTermsInclusion P := rfl

/-- The original forward identification is genuinely exact for the fine weak class. -/
theorem boundedAcyclicToFiberObjects_exact :
    IsExact (ofExactCategory (boundedAcyclicExactStructure P)).cof
      (ofExactCategory (boundedAcyclicExactStructure P)).weq
      (Fibration.acyclicStructure (boundedTermsNested P)).cof
      (Fibration.acyclicStructure (boundedTermsNested P)).weq
      (boundedAcyclicToFiberObjects P) where
  zero h := by
    let : (fiberObjectsToBoundedAcyclic P).IsEquivalence :=
      (boundedAcyclicFiberEquivalence P).isEquivalence_inverse
    exact IsZero.of_full_of_faithful_of_isZero (fiberObjectsToBoundedAcyclic P) _ h
  cofibration f hf := (boundedAcyclicTermsExactInclusion P).map_inflation f hf
  weak f hf := by
    let : IsIso f := hf
    change IsIso ((boundedAcyclicTermsInclusion P).map f)
    infer_instance
  pushout _ h := by
    let : (boundedAcyclicToFiberObjects P).IsEquivalence :=
      (boundedAcyclicFiberEquivalence P).isEquivalence_functor
    exact h.map (boundedAcyclicToFiberObjects P)

/-- The inverse is genuinely exact; inherited inflation reflection uses the
actual ambient acyclic quotient, not closure under arbitrary cokernels. -/
theorem fiberObjectsToBoundedAcyclic_exact :
    IsExact (Fibration.acyclicStructure (boundedTermsNested P)).cof
      (Fibration.acyclicStructure (boundedTermsNested P)).weq
      (ofExactCategory (boundedAcyclicExactStructure P)).cof
      (ofExactCategory (boundedAcyclicExactStructure P)).weq
      (fiberObjectsToBoundedAcyclic P) where
  zero h := by
    let : (boundedAcyclicToFiberObjects P).IsEquivalence :=
      (boundedAcyclicFiberEquivalence P).isEquivalence_functor
    exact IsZero.of_full_of_faithful_of_isZero (boundedAcyclicToFiberObjects P) _ h
  cofibration f hf := (boundedAcyclicTermsInclusion_inflation_iff P
    ((fiberObjectsToBoundedAcyclic P).map f)).1 hf
  weak f hf := by
    let : IsIso ((Fibration.acyclicObjects (boundedTermsNested P)).ι.map f) := hf
    let : IsIso f := isIso_of_reflects_iso f (Fibration.acyclicObjects (boundedTermsNested P)).ι
    exact (fiberObjectsToBoundedAcyclic P).map_isIso f
  pushout _ h := by
    let : (fiberObjectsToBoundedAcyclic P).IsEquivalence :=
      (boundedAcyclicFiberEquivalence P).isEquivalence_inverse
    exact h.map (fiberObjectsToBoundedAcyclic P)

end CategoryTheory.Waldhausen.GilletWaldhausen
