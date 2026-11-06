/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.FiniteSubcomplex
public import Colib.Topology.ClassifyingSpace.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# Exact finite full-subposet support in a poset nerve

A simplicial subcomplex of a poset nerve factors through the full subposet
on its actual vertices. When the subcomplex is finite, that vertex image is
finite. Exact compact support then factors every compact-source continuous map
through the classifying space of a finite full subposet, retaining the original
inclusion map. No subdivision or simplicial approximation is used.

Implementation provenance:
`Quillen/Topology/Realization/FinitePosetSupport.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses and universe parameters are retained.
-/
@[expose] public section


noncomputable section
open Topology TopCat SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open scoped Topology Simplicial
universe u v
namespace CategoryTheory.FiniteNervePosetSupport
variable {P : Type u} [PartialOrder P]

/-- The inclusion of the actual full subposet on a subset. -/
def inclusion (s : Set P) : s ⥤ P :=
  (show s →o P from ⟨Subtype.val, fun _ _ h => h⟩).monotone.functor

/-- The actual vertex image of the original simplicial subcomplex. -/
def vertices (A : (nerve P).Subcomplex) : Set P :=
  Set.range (fun a : A.toSSet.obj (op ⦋0⦌) => nerveEquiv a.val)

/-- Every vertex of every simplex is in the same actual vertex image. -/
theorem simplex_vertex_mem (A : (nerve P).Subcomplex) {n : SimplexCategoryᵒᵖ}
    (a : A.toSSet.obj n) (i : Fin (n.unop.len + 1)) : a.val.obj i ∈ vertices A := by
  refine ⟨A.toSSet.map (SimplexCategory.const ⦋0⦌ n.unop i).op a, ?_⟩
  rfl

/-- The original simplex, with only its vertices restricted to the actual image. -/
def factor (A : (nerve P).Subcomplex) : A.toSSet ⟶ nerve (vertices A) where
  app n := ↾fun a => {
    obj i := ⟨a.val.obj i, simplex_vertex_mem A a i⟩
    map h := homOfLE (leOfHom (a.val.map h)) }
  naturality n m f := by
    ext a i
    rfl

/-- The factorization preserves the original simplicial inclusion exactly. -/
theorem factor_comp_inclusion (A : (nerve P).Subcomplex) :
    factor A ≫ nerveMap (inclusion (vertices A)) = A.ι := by
  ext n a i
  rfl

/-- Finitely many nondegenerate simplices give a genuinely finite vertex image. -/
theorem vertices_finite (A : (nerve P).Subcomplex) [SSet.Finite A] :
    (vertices A).Finite := Set.finite_range _

/-- Exact finite full-subposet factorization of the original simplicial inclusion. -/
theorem finite_subcomplex_factors (A : (nerve P).Subcomplex) [SSet.Finite A] :
    ∃ s : Set P, s.Finite ∧ ∃ g : A.toSSet ⟶ nerve s,
      g ≫ nerveMap (inclusion s) = A.ι :=
  ⟨vertices A, vertices_finite A, factor A, factor_comp_inclusion A⟩

/-- Exact compact-source factorization through the classifying space of a
finite full subposet, with no countability or nonemptiness hypothesis. -/
theorem compactMap_factors {T : Type v} [TopologicalSpace T] [CompactSpace T]
    (f : C(T, ClassifyingSpace P)) :
    ∃ s : Set P, s.Finite ∧ ∃ g : C(T, ClassifyingSpace s),
      (classifyingSpaceMap (inclusion s)).hom.comp g = f := by
  obtain ⟨A, hA, g, hg⟩ := realization_continuousMap_factors_finiteSubcomplex f
  let : SSet.Finite A := hA
  refine ⟨vertices A, vertices_finite A,
    (SSet.toTop.map (factor A)).hom.comp g, ?_⟩
  change (SSet.toTop.map (nerveMap (inclusion (vertices A)))).hom.comp
    ((SSet.toTop.map (factor A)).hom.comp g) = f
  have he := congrArg (fun q => (SSet.toTop.map q).hom) (factor_comp_inclusion A)
  rw [Functor.map_comp] at he
  change (SSet.toTop.map (nerveMap (inclusion (vertices A)))).hom.comp
    (SSet.toTop.map (factor A)).hom = (SSet.toTop.map A.ι).hom at he
  rw [← ContinuousMap.comp_assoc, he]
  exact hg

end CategoryTheory.FiniteNervePosetSupport
