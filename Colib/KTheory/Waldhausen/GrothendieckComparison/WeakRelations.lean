/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.GrothendieckComparison.ObjectLoops
public import Colib.CategoryTheory.Waldhausen.Rows.NerveBridge
public import Colib.Topology.ClassifyingSpace.ArrowPaths

/-! # Original weak equivalences preserve actual Waldhausen object loops

The original weak one-row arrow determines the two genuine diagonal triangles
of its interval/nerve square. Their realized composition homotopies compare
the canonical source and target object loops.

Implementation provenance: `Quillen/Waldhausen/GrothendieckComparison/WeakRelations.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
objects, maps and hypotheses are retained.
-/
@[expose] public section

open CategoryTheory.Waldhausen.QuotientRows


noncomputable section
open Topology SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u v
namespace CategoryTheory.Waldhausen.Structure
open QuotientRows
variable {C : Type u} [Category.{v} C] (W : Structure C)
  {A B : C} (f : A ⟶ B) (hf : W.weq f)

/-- The original weak arrow between the actual one-step quotient rows. -/
def oneWeakArrow : (⟨(oneEmbedding W).obj A⟩ : WeakRows W ⦋1⦌) ⟶
    ⟨(oneEmbedding W).obj B⟩ :=
  ⟨(oneEmbedding W).map f, (oneEmbedding_exact W).weak f hf⟩

/-- The original weak-arrow square, read as a diagonal one-simplex. -/
def weakObjectSimplex : (sSet W.cof W.weq) _⦋1⦌ :=
  ⟨weakChainToGrid W (ComposableArrows.mk₁ (W.oneWeakArrow f hf)),
    (isSimplex₂_diagonal_iff W.cof W.weq _).mp (weakChainToGrid_isSimplex₂ W _)⟩

/-- Independently degenerate the original weak-arrow square in its two directions. -/
def weakObjectTriangle (i j : Fin 2) : (sSet W.cof W.weq) _⦋2⦌ :=
  ⟨gridMap₂ (SimplexCategory.σ i) (SimplexCategory.σ j) ⋙
      weakChainToGrid W (ComposableArrows.mk₁ (W.oneWeakArrow f hf)),
    (isSimplex₂_diagonal_iff W.cof W.weq _).mp
      ((weakChainToGrid_isSimplex₂ W _).precomp W.cof W.weq _ _)⟩

/-- The middle face of either triangulation is the unchanged original weak-arrow square. -/
theorem weakObjectTriangle_middle (i j : Fin 2) :
    (sSet W.cof W.weq).δ 1 (W.weakObjectTriangle f hf i j) = W.weakObjectSimplex f hf := by
  apply Subtype.ext
  change gridMap (SimplexCategory.δ 1) ⋙
    (gridMap₂ (SimplexCategory.σ i) (SimplexCategory.σ j) ⋙ _) = _
  have hidx : gridMap (SimplexCategory.δ 1) ⋙
      gridMap₂ (SimplexCategory.σ i) (SimplexCategory.σ j) = 𝟭 (Grid ⦋1⦌) := by
    apply CategoryTheory.Functor.ext (fun p ↦ ?_)
    rcases p with ⟨t, ⟨⟨a,b⟩, hab⟩⟩
    fin_cases i <;> fin_cases j <;> fin_cases t <;> fin_cases a <;> fin_cases b <;> rfl
  rw [← Functor.assoc, hidx, Functor.id_comp]
  rfl

/-- The first short edge of the upper triangle is the original source object simplex. -/
theorem weakObjectTriangle_source :
    (sSet W.cof W.weq).δ 2 (W.weakObjectTriangle f hf 1 0) = W.kZeroObjectSimplex A := by
  apply Subtype.ext
  change gridMap (SimplexCategory.δ 2) ⋙
    (gridMap₂ (SimplexCategory.σ 1) (SimplexCategory.σ 0) ⋙ _) = _
  have hidx : gridMap (SimplexCategory.δ 2) ⋙
      gridMap₂ (SimplexCategory.σ 1) (SimplexCategory.σ 0) =
        intervalProjection ⦋1⦌ ⋙ gridRestriction (n := ⦋1⦌) (m := ⦋1⦌) 0 := by
    apply CategoryTheory.Functor.ext (fun p ↦ ?_)
    rcases p with ⟨t, ⟨⟨a,b⟩, hab⟩⟩
    fin_cases t <;> fin_cases a <;> fin_cases b <;> rfl
  rw [← Functor.assoc, hidx, Functor.assoc, weakChainToGrid_row]
  rfl

/-- The second short edge of the lower triangle is the original target object simplex. -/
theorem weakObjectTriangle_target :
    (sSet W.cof W.weq).δ 0 (W.weakObjectTriangle f hf 0 1) = W.kZeroObjectSimplex B := by
  apply Subtype.ext
  change gridMap (SimplexCategory.δ 0) ⋙
    (gridMap₂ (SimplexCategory.σ 0) (SimplexCategory.σ 1) ⋙ _) = _
  have hidx : gridMap (SimplexCategory.δ 0) ⋙
      gridMap₂ (SimplexCategory.σ 0) (SimplexCategory.σ 1) =
        intervalProjection ⦋1⦌ ⋙ gridRestriction (n := ⦋1⦌) (m := ⦋1⦌) 1 := by
    apply CategoryTheory.Functor.ext (fun p ↦ ?_)
    rcases p with ⟨t, ⟨⟨a,b⟩, hab⟩⟩
    fin_cases t <;> fin_cases a <;> fin_cases b <;> rfl
  rw [← Functor.assoc, hidx, Functor.assoc, weakChainToGrid_row]
  rfl

/-- The remaining upper boundary edge is literally the chosen zero simplex. -/
theorem weakObjectTriangle_upper_zero :
    (sSet W.cof W.weq).δ 0 (W.weakObjectTriangle f hf 1 0) =
      zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋1⦌) := by
  apply Subtype.ext
  have hobj : ∀ p,
      ((sSet W.cof W.weq).δ 0 (W.weakObjectTriangle f hf 1 0)).val.obj p = W.zero := by
    rintro ⟨t, ⟨⟨a,b⟩, hab⟩⟩
    fin_cases t <;> fin_cases a <;> fin_cases b <;> rfl
  refine CategoryTheory.Functor.ext hobj ?_
  intro p q g
  have hz : IsZero (((sSet W.cof W.weq).δ 0 (W.weakObjectTriangle f hf 1 0)).val.obj p) := by
    rw [hobj p]
    exact W.isZero
  exact hz.eq_of_src _ _

/-- The remaining lower boundary edge is literally the chosen zero simplex. -/
theorem weakObjectTriangle_lower_zero :
    (sSet W.cof W.weq).δ 2 (W.weakObjectTriangle f hf 0 1) =
      zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋1⦌) := by
  apply Subtype.ext
  have hobj : ∀ p,
      ((sSet W.cof W.weq).δ 2 (W.weakObjectTriangle f hf 0 1)).val.obj p = W.zero := by
    rintro ⟨t, ⟨⟨a,b⟩, hab⟩⟩
    fin_cases t <;> fin_cases a <;> fin_cases b <;> rfl
  refine CategoryTheory.Functor.ext hobj ?_
  intro p q g
  have hz : IsZero (((sSet W.cof W.weq).δ 2 (W.weakObjectTriangle f hf 0 1)).val.obj p) := by
    rw [hobj p]
    exact W.isZero
  exact hz.eq_of_src _ _

/-- Both endpoints of the original weak-arrow edge are the literal chosen zero vertex. -/
theorem weakObjectSimplex_δ (i : Fin 2) :
    (sSet W.cof W.weq).δ i (W.weakObjectSimplex f hf) =
      zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌) := by
  apply Subtype.ext
  have hobj : ∀ p,
      ((sSet W.cof W.weq).δ i (W.weakObjectSimplex f hf)).val.obj p = W.zero := by
    rintro ⟨t, ⟨⟨a,b⟩, hab⟩⟩
    fin_cases t; fin_cases a; fin_cases b; fin_cases i <;> rfl
  refine CategoryTheory.Functor.ext hobj ?_
  intro p q g
  have hz : IsZero (((sSet W.cof W.weq).δ i (W.weakObjectSimplex f hf)).val.obj p) := by
    rw [hobj p]
    exact W.isZero
  exact hz.eq_of_src _ _

/-- The original weak-arrow square as an actual based edge. -/
def weakObjectEdge :
    (sSet W.cof W.weq).Edge
      (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌))
      (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌)) where
  edge := W.weakObjectSimplex f hf
  src_eq := W.weakObjectSimplex_δ f hf 1
  tgt_eq := W.weakObjectSimplex_δ f hf 0

/-- The genuine upper diagonal triangle composes the original source loop with zero. -/
def weakObjectUpperCompStruct : SSet.Edge.CompStruct (W.kZeroObjectEdge A)
    (SSet.Edge.id (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌)))
    (W.weakObjectEdge f hf) where
  simplex := W.weakObjectTriangle f hf 1 0
  d₂ := W.weakObjectTriangle_source f hf
  d₀ := W.weakObjectTriangle_upper_zero f hf
  d₁ := W.weakObjectTriangle_middle f hf 1 0

/-- The genuine lower diagonal triangle composes zero with the original target loop. -/
def weakObjectLowerCompStruct : SSet.Edge.CompStruct
    (SSet.Edge.id (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌)))
    (W.kZeroObjectEdge B) (W.weakObjectEdge f hf) where
  simplex := W.weakObjectTriangle f hf 0 1
  d₂ := W.weakObjectTriangle_lower_zero f hf
  d₀ := W.weakObjectTriangle_target f hf
  d₁ := W.weakObjectTriangle_middle f hf 0 1

include hf in
/-- An original weak arrow gives an actual endpoint-fixed homotopy between
its original canonical source and target object loops. -/
theorem kZeroObjectLoop_weak_homotopic :
    (W.kZeroObjectLoop A).Homotopic (W.kZeroObjectLoop B) := by
  have hA := realizationEdgePath_comp (W.weakObjectUpperCompStruct f hf)
  have hB := realizationEdgePath_comp (W.weakObjectLowerCompStruct f hf)
  rw [realizationEdgePath_id] at hA hB
  exact ((Path.Homotopic.trans_refl (W.kZeroObjectLoop A)).symm.trans hA).trans
    (((Path.Homotopic.refl_trans (W.kZeroObjectLoop B)).symm.trans hB).symm)

include hf in
/-- Original weak equivalences identify the actual original homotopical object
classes, proved by genuine diagonal simplices rather than by an assumed presentation. -/
theorem kZeroObjectClass_weak : W.kZeroObjectClass A = W.kZeroObjectClass B := by
  apply W.kZeroFundamentalGroupEquiv.injective
  rw [W.kZeroFundamentalGroupEquiv_objectClass, W.kZeroFundamentalGroupEquiv_objectClass]
  apply End.ext
  exact Quotient.sound (W.kZeroObjectLoop_weak_homotopic f hf)

/-- Original categorical isomorphisms preserve the actual canonical object class. -/
theorem kZeroObjectClass_iso (e : A ≅ B) : W.kZeroObjectClass A = W.kZeroObjectClass B :=
  W.kZeroObjectClass_weak e.hom (W.weq_iso e.hom inferInstance)

/-- Any actual zero object, not just the chosen one, has trivial canonical class. -/
theorem kZeroObjectClass_of_isZero (Z : C) (hZ : IsZero Z) : W.kZeroObjectClass Z = 1 :=
  (W.kZeroObjectClass_iso (hZ.iso W.isZero)).trans W.kZeroObjectClass_zero

end CategoryTheory.Waldhausen.Structure
