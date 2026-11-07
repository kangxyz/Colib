/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.CategoryTheory.Abelian.Devissage.LayerFunctors
public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.Abelian.Devissage.Filtration
public import Colib.Topology.ClassifyingSpace.Adjunction
public import Colib.Topology.ClassifyingSpace.Contraction

/-!
# Contraction of the dévissage layer category

Intersection gives the one-step homotopy equivalence in Quillen's proof.
Induction over an actual finite filtration then contracts the layer category.
-/
/-!
Implementation provenance: adapted from
`Quillen/Devissage/LayerContraction.lean` at Quillen
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
Native Mathlib full subcategories, Colib exact structures,
restricted spans, actual realization maps and their universes are retained.
No extension-closure, uniform filtration bound, alternate K-model or Aglib import is added.
-/

@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
universe v u
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace CategoryTheory.Abelian.Devissage
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]
  (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderSubobjects]
  [P.IsClosedUnderQuotients] [P.IsClosedUnderFiniteProducts]

namespace Layer
variable {P} {M : C}

/-- Quillen's one-filtration-step equivalence, with actual continuous homotopies
and the inclusion as its forward map. -/
def supportedStepHomotopyEquiv {A N : Subobject M} (hAN : A ≤ N)
    (hA : P (cokernel (Subobject.ofLE A N hAN))) :
    ContinuousMap.HomotopyEquiv
      (ClassifyingSpace (Supported (P := P) A))
      (ClassifyingSpace (Supported (P := P) N)) where
  toFun := (classifyingSpaceMap (supportedInclusion (P := P) hAN)).hom
  invFun := (classifyingSpaceMap (supportedRestriction (P := P) A N)).hom
  left_inv := by
    simpa only [classifyingSpaceMap_comp, classifyingSpaceMap_id, TopCat.hom_comp,
      TopCat.hom_id] using
      (show (classifyingSpaceMap (supportedInclusion (P := P) hAN ⋙
        supportedRestriction A N)).hom.Homotopic
          (classifyingSpaceMap (𝟭 (Supported (P := P) A))).hom from
        ⟨classifyingSpaceNaturalTransformationHomotopy
          (supportedRestrictionUnit (P := P) hAN).hom⟩)
  right_inv := by
    have h₁ := classifyingSpaceNaturalTransformationHomotopy
      (supportedRestrictionToEnlargement (P := P) hAN hA)
    have h₂ := classifyingSpaceNaturalTransformationHomotopy
      (supportedIdToEnlargement (P := P) hAN hA)
    simpa only [classifyingSpaceMap_comp, classifyingSpaceMap_id, TopCat.hom_comp,
      TopCat.hom_id] using (ContinuousMap.Homotopic.trans ⟨h₁⟩ ⟨h₂.symm⟩)

omit [P.IsClosedUnderSubobjects] [P.IsClosedUnderFiniteProducts] in
/-- The base of finite-filtration induction is genuinely contractible. -/
theorem supportedBottom_contractible :
    ContractibleSpace (ClassifyingSpace (Supported (P := P) (⊥ : Subobject M))) :=
  classifyingSpace_contractible_of_isTerminal (supportedBottomIsTerminal (P := P))

/-- Any finite admissible filtration contracts the layer category supported
on its image under any ambient monomorphism. -/
theorem supported_contractible_of_filtration {X M : C}
    (F : (abelianExactStructure C).Filtration P X) (j : X ⟶ M) [Mono j] :
    ContractibleSpace (ClassifyingSpace (Supported (P := P) (Subobject.mk j))) := by
  induction F generalizing M with
  | zero hX =>
    have h : Subobject.mk j = ⊥ := Subobject.mk_eq_bot_iff_zero.mpr (hX.eq_of_src _ _)
    rw [h]
    exact supportedBottom_contractible
  | step S hS F hP ih =>
    have hS' : S.ShortExact := hS
    let := hS'.mono_f
    let A := Subobject.mk (S.f ≫ j)
    let N := Subobject.mk j
    have hAN : A ≤ N := Subobject.mk_le_mk_of_comm S.f rfl
    let e : cokernel (Subobject.ofLE A N hAN) ≅ cokernel S.f :=
      cokernel.mapIso _ _ (Subobject.underlyingIso (S.f ≫ j))
        (Subobject.underlyingIso j) (by
          apply (cancel_mono j).1
          simp [A, N, assoc])
    let e' : cokernel S.f ≅ S.X₃ :=
      (cokernelIsCokernel S.f).coconePointUniqueUpToIso hS'.gIsCokernel
    have hA : P (cokernel (Subobject.ofLE A N hAN)) :=
      P.prop_of_iso (e.trans e').symm hP
    let : ContractibleSpace (ClassifyingSpace (Supported (P := P) A)) := ih (S.f ≫ j)
    exact (supportedStepHomotopyEquiv hAN hA).symm.contractibleSpace

/-- The layer category in Quillen's dévissage proof is contractible whenever
the ambient object has a finite filtration with factors in `P`. -/
theorem contractible_of_filtration {M : C}
    (F : (abelianExactStructure C).Filtration P M) :
    ContractibleSpace (ClassifyingSpace (Layer P M)) := by
  have h := supported_contractible_of_filtration F (𝟙 M)
  rw [Subobject.mk_eq_top_of_isIso] at h
  let := h
  exact (equivalenceClassifyingHomotopyEquiv
    (supportedTopEquivalence (P := P) (M := M))).symm.contractibleSpace

end Layer
end CategoryTheory.Abelian.Devissage

attribute [colib_ref "WeibelKBook"
  "V, Devissage Theorem 4.1, intersection contraction in the proof, page 33"
  "adaptation" "The intersection zigzag and finite-filtration induction give actual contractions"]
  CategoryTheory.Abelian.Devissage.Layer.supportedStepHomotopyEquiv
  CategoryTheory.Abelian.Devissage.Layer.supported_contractible_of_filtration
  CategoryTheory.Abelian.Devissage.Layer.contractible_of_filtration
