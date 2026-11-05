/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.OrdinalSubdivisionSimplex
public import Colib.Topology.ClassifyingSpace.Contraction
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Preorder

/-! # Ordinary subdivision equivalence on actual representable simplices

Selected and adapted from `Quillen/Topology/Realization/OrdinalSubdivisionRealization.lean`
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The two explicit contractions
prove equivalence for representables. The forward map is the first-half endpoint
for the unreversed indexing functor `[n] ↦ [n] ⋆ [n]`.

This file does not claim an equivalence for every simplicial set. Extending the
result requires the actual cellular pushout and sequential homotopy-invariance
arguments; preservation of colimits alone does not imply that extension.
-/
@[expose] public noncomputable section
open CategoryTheory Limits Opposite
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SSet.OrdinalSubdivision

instance subdivisionFunctor_preservesColimits : PreservesColimits subdivisionFunctor.{u} := by
  unfold subdivisionFunctor
  infer_instance

instance subdivisionFunctor_preservesSequentialColimits :
    PreservesColimitsOfShape ℕ subdivisionFunctor.{u} := by
  unfold subdivisionFunctor
  infer_instance

instance subdivisionFunctor_preservesMonomorphisms :
    subdivisionFunctor.{u}.PreservesMonomorphisms where
  preserves {X Y} f hf := by
    have : ∀ n, Mono ((subdivisionFunctor.map f).app n) := fun n ↦ by
      change Mono (f.app (δ.op.obj n))
      infer_instance
    exact NatTrans.mono_of_mono_app _

private theorem homotopic_into_contractible {A B : Type u}
    [TopologicalSpace A] [TopologicalSpace B] [ContractibleSpace B]
    (f g : C(A, B)) : f.Homotopic g := by
  obtain ⟨b, h⟩ := id_nullhomotopic B
  have hf : f.Homotopic (ContinuousMap.const A b) :=
    h.comp (ContinuousMap.Homotopic.refl f)
  have hg : g.Homotopic (ContinuousMap.const A b) :=
    h.comp (ContinuousMap.Homotopic.refl g)
  exact hf.trans hg.symm

/-- The genuine endpoint map is a realization equivalence on every representable. -/
theorem realizesEquiv_endpoint_simplex (n : ℕ) :
    ∃ e : ContinuousMap.HomotopyEquiv |subdivision (Δ[n] : SSet.{u})| |(Δ[n] : SSet.{u})|,
      e.toFun = (SSet.toTop.map (endpoint (Δ[n] : SSet.{u}))).hom := by
  let : ContractibleSpace |subdivision (Δ[n] : SSet.{u})| :=
    contractibleSpace_simplex.{u} n
  let : ContractibleSpace |nerve (ULift.{u} (Fin (n + 1)))| := by
    change ContractibleSpace (ClassifyingSpace (ULift.{u} (Fin (n + 1))))
    infer_instance
  let : ContractibleSpace |(Δ[n] : SSet.{u})| :=
    (TopCat.homeoOfIso (SSet.toTop.mapIso (SSet.stdSimplex.isoNerve n))).contractibleSpace
  refine ⟨{
    toFun := (SSet.toTop.map (endpoint (Δ[n] : SSet.{u}))).hom
    invFun := ContinuousMap.const _ (realizationPoint (simplexVertex n))
    left_inv := homotopic_into_contractible _ _
    right_inv := homotopic_into_contractible _ _ }, rfl⟩

/-- The endpoint equivalence on a representable, with the actual endpoint as forward map. -/
def simplexRealizationHomotopyEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv |subdivision (Δ[n] : SSet.{u})| |(Δ[n] : SSet.{u})| := by
  let e := (realizesEquiv_endpoint_simplex.{u} n).choose
  have he := (realizesEquiv_endpoint_simplex.{u} n).choose_spec
  exact { e with
    toFun := (SSet.toTop.map (endpoint (Δ[n] : SSet.{u}))).hom
    left_inv := by rw [← he]; exact e.left_inv
    right_inv := by rw [← he]; exact e.right_inv }

@[simp] theorem simplexRealizationHomotopyEquiv_toFun (n : ℕ) :
    (simplexRealizationHomotopyEquiv.{u} n).toFun =
      (SSet.toTop.map (endpoint (Δ[n] : SSet.{u}))).hom := rfl

/-- The realized first-half endpoint is natural for arbitrary simplicial maps. -/
theorem realization_endpoint_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    SSet.toTop.map (subdivisionFunctor.map f) ≫ SSet.toTop.map (endpoint Y) =
      SSet.toTop.map (endpoint X) ≫ SSet.toTop.map f := by
  have h := endpointNatTrans.naturality f
  change subdivisionFunctor.map f ≫ endpoint Y = endpoint X ≫ f at h
  simpa only [Functor.map_comp] using congrArg SSet.toTop.map h

/-- A vertex of a simplicial set determines the degenerate interval vertex
of its ordinary twofold subdivision. -/
def vertex {X : SSet.{u}} (x : X _⦋0⦌) : (subdivision X) _⦋0⦌ := X.σ 0 x

@[simp] theorem endpoint_vertex {X : SSet.{u}} (x : X _⦋0⦌) :
    (endpoint X).app _ (vertex x) = x := by
  have hr : first.app ⦋0⦌ = SimplexCategory.δ 1 := by
    ext i : 3
    have hi : i = 0 := by
      exact @Subsingleton.elim (Fin 1) inferInstance i 0
    subst i
    rfl
  change X.map (first.app ⦋0⦌).op (X.σ 0 x) = x
  rw [hr]
  change X.δ 1 (X.σ 0 x) = x
  exact X.δ_comp_σ_succ_apply 0 x

end SSet.OrdinalSubdivision
