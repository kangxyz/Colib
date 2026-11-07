/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Rows.OneRow
public import Colib.CategoryTheory.Waldhausen.SMap
public import Colib.CategoryTheory.Waldhausen.SConstruction.Zero
public import Colib.AlgebraicTopology.SimplicialSet.Diagonal
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal


/-!
# The actual second S-stage and its suspension cylinder

The second stage is the diagonal of the original S-constructions on genuine
quotient-row Waldhausen categories. The original exact one-row embedding,
restricted along an actual ordinal map to `[1]`, constructs the simplicial
cylinder from the first stage. Both endpoint maps and the zero input are
proved to be the literal chosen zero rows. No delooping equivalence is assumed.

This is a concrete structural map prerequisite for the iterated-S spectrum
of Waldhausen, recalled in Thomason--Trobaugh, Section 1.5.3.
-/
/-!
## Implementation provenance

Adapted from `Quillen/Waldhausen/SConstruction/Iterated/Double.lean` at
Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual quotient-row
construction, maps, chosen zero objects, hypotheses and universes are retained.
Native Colib simplicial, realization and homotopy-group owners are reused.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial MonoidalCategory
universe u v
namespace CategoryTheory.Waldhausen.IteratedS
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- The genuine second S-stage before taking its final diagonal. -/
def doubleS : SimplexCategoryᵒᵖ ⥤ SSet.{max u v} where
  obj n := sSet (QuotientRows.waldhausenStructure W n.unop).cof
    (QuotientRows.waldhausenStructure W n.unop).weq
  map α := sSetMap (QuotientRows.reindex_exact W α.unop)
  map_id n := by
    ext k A : 4
    apply Subtype.ext
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
  map_comp α β := by
    ext k A : 4
    apply Subtype.ext
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The actual diagonal of the iterated quotient-row construction. -/
def doubleDiagonal : SSet.{max u v} := SSet.diagonalSSet (doubleS W)

/-- The original one-step row inserted at an actual ordinal parameter. -/
def suspensionRow {n : SimplexCategory} (τ : n ⟶ ⦋1⦌) : C ⥤ QuotientRows.Obj W n :=
  QuotientRows.oneEmbedding W ⋙ QuotientRows.reindex W τ

lemma suspensionRow_exact {n : SimplexCategory} (τ : n ⟶ ⦋1⦌) :
    IsExact W.cof W.weq (QuotientRows.waldhausenStructure W n).cof
      (QuotientRows.waldhausenStructure W n).weq (suspensionRow W τ) :=
  (QuotientRows.oneEmbedding_exact W).comp (QuotientRows.reindex_exact W τ)

lemma suspensionRow_reindex {m n : SimplexCategory} (α : m ⟶ n) (τ : n ⟶ ⦋1⦌) :
    suspensionRow W (α ≫ τ) = suspensionRow W τ ⋙ QuotientRows.reindex W α := by
  rw [suspensionRow, QuotientRows.reindex_comp]
  rfl

lemma suspensionRow_const_obj (n : SimplexCategory) (c : Fin 2) (X : C) :
    (suspensionRow W (SimplexCategory.const n ⦋1⦌ c)).obj X = QuotientRows.zero W n := by
  apply ObjectProperty.FullSubcategory.ext
  fin_cases c <;>
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  all_goals intro p q f; exact W.isZero.eq_of_src _ _

lemma suspensionRow_const (n : SimplexCategory) (c : Fin 2) :
    suspensionRow W (SimplexCategory.const n ⦋1⦌ c) =
      (Functor.const C).obj (QuotientRows.zero W n) := by
  refine CategoryTheory.Functor.ext (suspensionRow_const_obj W n c) ?_
  intro X Y f
  exact ((QuotientRows.isZero W n).of_iso
    (eqToIso (suspensionRow_const_obj W n c X))).eq_of_src _ _

lemma suspensionRow_zero_obj {n : SimplexCategory} (τ : n ⟶ ⦋1⦌) :
    (suspensionRow W τ).obj W.zero = QuotientRows.zero W n := by
  have h : (QuotientRows.oneEmbedding W).obj W.zero = QuotientRows.zero W ⦋1⦌ := by
    apply ObjectProperty.FullSubcategory.ext
    refine CategoryTheory.Functor.ext ?_ ?_
    · rintro ⟨⟨i,j⟩,hij⟩
      fin_cases i <;> fin_cases j <;> rfl
    · intro p q f
      exact (QuotientRows.evaluation_isZero W
        ((QuotientRows.oneEmbedding_exact W).zero W.isZero) p).eq_of_src _ _
  change (QuotientRows.reindex W τ).obj ((QuotientRows.oneEmbedding W).obj W.zero) = _
  rw [h, QuotientRows.reindex_zero]

/-- The concrete simplicial suspension precursor. Both interval endpoints
will be the original zero row; no delooping equivalence is part of the definition. -/
def suspensionCylinder : sSet W.cof W.weq ⊗ Δ[1] ⟶ doubleDiagonal W where
  app n := ↾fun z ↦ ⟨z.1.val ⋙ suspensionRow W z.2.down,
    z.1.property.postcomp (suspensionRow_exact W z.2.down)⟩
  naturality n m α := by
    ext z : 3
    apply Subtype.ext
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The chosen zero rows define the actual basepoint simplicial map. -/
def doubleZero : sSet W.cof W.weq ⟶ doubleDiagonal W where
  app n := ↾fun _ ↦ zeroSimplex (QuotientRows.waldhausenStructure W n.unop).cof
    (QuotientRows.waldhausenStructure W n.unop).weq
    (QuotientRows.zero W n.unop) (QuotientRows.isZero W n.unop) n
  naturality n m α := by
    ext z : 3
    apply Subtype.ext
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

lemma suspensionCylinder_endpoint (n : SimplexCategoryᵒᵖ)
    (A : (sSet W.cof W.weq).obj n) (c : Fin 2) :
    (suspensionCylinder W).app n (A, ⟨SimplexCategory.const n.unop ⦋1⦌ c⟩) =
      (doubleZero W).app n A := by
  apply Subtype.ext
  change A.val ⋙ suspensionRow W (SimplexCategory.const n.unop ⦋1⦌ c) = _
  rw [suspensionRow_const]
  rfl

@[simp] lemma suspensionCylinder_zero :
    SSet.ι₀ ≫ suspensionCylinder W = doubleZero W := by
  ext n A : 4
  exact suspensionCylinder_endpoint W n A 0

@[simp] lemma suspensionCylinder_one :
    SSet.ι₁ ≫ suspensionCylinder W = doubleZero W := by
  ext n A : 4
  exact suspensionCylinder_endpoint W n A 1

end CategoryTheory.Waldhausen.IteratedS
