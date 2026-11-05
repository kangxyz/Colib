/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.Topology.Realization.Coproduct
public import Colib.Topology.Realization.Basic

/-!
# Constant simplicial sets realize to their discrete values

The canonical isomorphism is assembled from the actual coproduct of standard
zero-simplices. Its forward map sends the realized vertex to its value and is
natural for every map of indexing types, including empty types.

## Implementation provenance

Selected from `Quillen/CategoryTheory/TheoremA/ColumnRealization.lean`,
`Quillen/CategoryTheory/TheoremB/TotalProjection.lean`, and
`Quillen/Topology/ClassifyingSpace/DiscretePoints.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Only the generic constant-realization
construction and point formula are extracted. No theorem A/B assumptions,
coends, replacement projections or homotopy-group conclusions are imported.
The source maps, proofs and universe parameters are retained.
-/
@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial Topology

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace TopCat

/-- A topological coproduct of points is the discrete index space. -/
def sigmaPointHomeomorph (A : Type u) :
    (Σ _a : A, |(Δ[0] : SSet.{u})|) ≃ₜ TopCat.discrete.obj A where
  toFun := Sigma.fst
  invFun a := ⟨a, default⟩
  left_inv := by
    rintro ⟨a, x⟩
    exact congrArg (Sigma.mk a) (Subsingleton.elim _ _)
  right_inv a := rfl
  continuous_toFun := continuous_sigma fun _ ↦ continuous_const
  continuous_invFun := continuous_of_discreteTopology

end TopCat

namespace SSet

/-- The unique simplex of the standard zero-simplex in each simplicial degree. -/
local instance pointSimplexUnique (p : SimplexCategoryᵒᵖ) :
    Unique ((Δ[0] : SSet.{u}).obj p) := (SSet.stdSimplex.objEquiv (n := ⦋0⦌) (m := p)).unique

/-- A disjoint union of point simplicial sets is the constant simplicial set
on its indexing type. -/
def pointSigmaIso (A : Type u) :
    SSet.simplicialSigma (fun _ : A ↦ (Δ[0] : SSet.{u})) ≅
      (Functor.const SimplexCategoryᵒᵖ).obj A :=
  NatIso.ofComponents (fun p ↦ Equiv.toIso
    { toFun := fun x ↦ x.1
      invFun := fun a ↦ ⟨a, default⟩
      left_inv := fun x ↦ by
        rcases x with ⟨i, x⟩
        exact congrArg (Sigma.mk i) (Subsingleton.elim _ _)
      right_inv := fun _ ↦ rfl }) (by
    intro p q α
    ext x : 3
    rfl)

/-- Realization of a constant simplicial set is its discrete space of
values, with the genuine geometric-realization topology. -/
def constantRealizationIso (A : Type u) :
    SSet.toTop.obj ((Functor.const SimplexCategoryᵒᵖ).obj A) ≅ TopCat.discrete.obj A :=
  (SSet.toTop.mapIso (pointSigmaIso A)).symm ≪≫
    SSet.realizationSigmaIso (fun _ : A ↦ (Δ[0] : SSet.{u})) ≪≫
      TopCat.isoOfHomeo (TopCat.sigmaPointHomeomorph A)

/-- The realized summand comparison, with the mapped composition expanded. -/
@[reassoc (attr := simp)]
theorem constantRealizationIso_ι_comp (A : Type u) (a : A) :
    SSet.toTop.map (SSet.simplicialSigmaι (fun _ : A ↦ (Δ[0] : SSet.{u})) a) ≫
      SSet.toTop.map (pointSigmaIso A).hom ≫ (constantRealizationIso A).hom =
      TopCat.ofHom (ContinuousMap.const |(Δ[0] : SSet.{u})|
        (show TopCat.discrete.obj A from a)) := by
  simp only [constantRealizationIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv]
  rw [← Category.assoc (SSet.toTop.map (pointSigmaIso A).hom),
    ← Functor.map_comp]
  simp only [Iso.hom_inv_id]
  rw [SSet.toTop.map_id, Category.id_comp, SSet.realizationSigmaIso_ι_assoc]
  rfl

/-- The discrete realization homeomorphisms respect arbitrary index maps. -/
theorem constantRealizationIso_naturality {A B : Type u} (f : A ⟶ B) :
    SSet.toTop.map ((Functor.const SimplexCategoryᵒᵖ).map f) ≫ (constantRealizationIso B).hom =
      (constantRealizationIso A).hom ≫ TopCat.discrete.map f := by
  apply (cancel_epi (SSet.toTop.map (pointSigmaIso A).hom)).mp
  apply (SSet.realizedSigmaIsColimit (fun _ : A ↦ (Δ[0] : SSet.{u}))).hom_ext
  intro ⟨a⟩
  dsimp
  have heq : SSet.simplicialSigmaι (fun _ : A ↦ (Δ[0] : SSet.{u})) a ≫
      (pointSigmaIso A).hom ≫ (Functor.const SimplexCategoryᵒᵖ).map f =
    SSet.simplicialSigmaι (fun _ : B ↦ (Δ[0] : SSet.{u})) (f a) ≫
      (pointSigmaIso B).hom := rfl
  simp only [← Category.assoc, ← Functor.map_comp]
  rw [Category.assoc (SSet.simplicialSigmaι _ a), heq]
  simp only [Functor.map_comp, Category.assoc, constantRealizationIso_ι_comp]
  rfl

/-- The canonical discrete-realization comparison sends the actual vertex to its value. -/
lemma constantRealizationIso_point (A : Type u) (a : A) :
    (constantRealizationIso A).hom
      (realizationPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj A) a) = a := by
  have e : SSet.simplicialSigmaι (fun _ : A ↦ (Δ[0] : SSet.{u})) a ≫
      (pointSigmaIso A).hom =
      (SSet.yonedaEquiv (X := (Functor.const SimplexCategoryᵒᵖ).obj A) (n := ⦋0⦌)).symm a := by
    apply SSet.yonedaEquiv.injective
    simp only [Equiv.apply_symm_apply]
    rfl
  have he := constantRealizationIso_ι_comp A a
  rw [← Category.assoc, ← Functor.map_comp] at he
  have h := ConcreteCategory.congr_hom he default
  rw [e] at h
  exact h

end SSet

attribute [colib_tag "COL-0091",
  colib_ref "WeibelKBook" "IV, Characterization 3.1(2),(5) and Definition 3.1.4, pages 24-25"
    "background"
    "Point realizations and discrete coproducts, with actual vertices and naturality"]
  SSet.constantRealizationIso
  SSet.constantRealizationIso_naturality
  SSet.constantRealizationIso_point
