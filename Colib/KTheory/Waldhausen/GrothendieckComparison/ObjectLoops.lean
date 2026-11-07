/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Basic
public import Colib.CategoryTheory.Waldhausen.Rows.OneRow
public import Colib.Topology.Realization.EdgePath

/-! # Canonical object loops in the genuine Waldhausen S-construction

For every Waldhausen structure, its genuine one-step quotient row is constant
in the nerve direction and gives a based edge in the original diagonal
S-construction. Its realized based loop gives the canonical object class in
the already-defined homotopy group K₀, without a presentation assumption.

Implementation provenance: `Quillen/Waldhausen/GrothendieckComparison/ObjectLoops.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
objects, maps and hypotheses are retained.
-/
@[expose] public section

noncomputable section
open Topology SSet
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Structure
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- Forget the nerve coordinate of a diagonal grid. -/
def intervalProjection (n : SimplexCategory) : Grid n ⥤ Interval n :=
  (show Monotone (fun p : Grid n ↦ p.2) from fun _ _ h ↦ h.2).functor

/-- A genuine quotient row repeated identically in the nerve direction. -/
def rowSimplex {n : SimplexCategory} (F : QuotientRows.Obj W n) :
    (sSet W.cof W.weq).obj (op n) :=
  ⟨intervalProjection n ⋙ F.obj, {
    zero _ i := F.property.zero i
    cofibration _ i j k hij hjk := F.property.cofibration i j k hij hjk
    quotient _ i j k hij hjk := F.property.quotient i j k hij hjk
    weak s t i j hst hij := by
      change W.weq (F.obj.map (𝟙 (interval i j hij)))
      rw [F.obj.map_id]
      exact W.weq.id_mem (F.obj.obj (interval i j hij)) }⟩

/-- The genuine diagonal 1-simplex whose original quotient row is `(0,X,0)`. -/
def kZeroObjectSimplex (X : C) : (sSet W.cof W.weq) _⦋1⦌ :=
  rowSimplex W ((QuotientRows.oneEmbedding W).obj X)

@[simp] theorem kZeroObjectSimplex_whole (X : C) (t : Fin 2) :
    (W.kZeroObjectSimplex X).val.obj (grid t 0 1 (by decide)) = X := rfl

@[simp] theorem kZeroObjectSimplex_zero :
    W.kZeroObjectSimplex W.zero =
      zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋1⦌) := by
  apply Subtype.ext
  have hobj : ∀ p, (W.kZeroObjectSimplex W.zero).val.obj p =
      (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋1⦌)).val.obj p := by
    rintro ⟨t, ⟨⟨a,b⟩, hab⟩⟩
    fin_cases a <;> fin_cases b <;> rfl
  refine CategoryTheory.Functor.ext hobj ?_
  intro p q f
  have hz : IsZero ((W.kZeroObjectSimplex W.zero).val.obj p) := by
    rw [hobj p]
    exact W.isZero
  exact hz.eq_of_src _ _

@[simp] theorem kZeroObjectSimplex_δ (X : C) (i : Fin 2) :
    (sSet W.cof W.weq).δ i (W.kZeroObjectSimplex X) =
      zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌) := by
  apply Subtype.ext
  have hobj : ∀ p, ((sSet W.cof W.weq).δ i (W.kZeroObjectSimplex X)).val.obj p =
      (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌)).val.obj p := by
    rintro ⟨t, ⟨⟨a,b⟩, hab⟩⟩
    fin_cases t; fin_cases a; fin_cases b; fin_cases i <;> rfl
  refine CategoryTheory.Functor.ext hobj ?_
  intro p q f
  have hs : ∀ p : Grid ⦋0⦌, p = grid 0 0 0 (by decide) := by
    rintro ⟨t, ⟨⟨a,b⟩, hab⟩⟩
    fin_cases t; fin_cases a; fin_cases b; rfl
  have hp := hs p
  have hq := hs q
  subst p; subst q
  have hf : f = 𝟙 _ := Subsingleton.elim _ _
  subst f
  simp

/-- The actual based edge of the original diagonal S-construction. -/
def kZeroObjectEdge (X : C) :
    (sSet W.cof W.weq).Edge
      (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌))
      (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌)) where
  edge := W.kZeroObjectSimplex X
  src_eq :=  W.kZeroObjectSimplex_δ X 1
  tgt_eq :=  W.kZeroObjectSimplex_δ X 0

@[simp] theorem kZeroObjectEdge_edge (X : C) :
    (W.kZeroObjectEdge X).edge = W.kZeroObjectSimplex X := rfl

@[simp] theorem kZeroObjectEdge_zero :
    W.kZeroObjectEdge W.zero =
      SSet.Edge.id (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌)) := by
  apply SSet.Truncated.Edge.ext
  exact W.kZeroObjectSimplex_zero

/-- The canonical loop is the realization of that exact based edge. -/
def kZeroObjectLoop (X : C) : Path W.kBasepoint W.kBasepoint :=
  realizationEdgePath (W.kZeroObjectEdge X)

@[simp] theorem kZeroObjectLoop_apply (X : C) (t : unitInterval) :
    W.kZeroObjectLoop X t = SSet.toTop.map
      (SSet.yonedaEquiv.symm (W.kZeroObjectSimplex X)) (realizationInterval t) := rfl

theorem kZeroObjectLoop_source (X : C) :
    W.kZeroObjectLoop X 0 = W.kBasepoint := (W.kZeroObjectLoop X).source

theorem kZeroObjectLoop_target (X : C) :
    W.kZeroObjectLoop X 1 = W.kBasepoint := (W.kZeroObjectLoop X).target

@[simp] theorem kZeroObjectLoop_zero :
    W.kZeroObjectLoop W.zero = Path.refl W.kBasepoint := by
  exact congrArg realizationEdgePath W.kZeroObjectEdge_zero |>.trans (realizationEdgePath_id _)

/-- Identify the original π₁ with based paths modulo based homotopy. -/
def kZeroFundamentalGroupEquiv :
    W.K 0 ≃* FundamentalGroup W.Delooping W.kBasepoint :=
  HomotopyGroup.pi1MulEquivFundamentalGroup

/-- An object class in the original homotopical Waldhausen K₀. -/
def kZeroObjectClass (X : C) : W.K 0 :=
  W.kZeroFundamentalGroupEquiv.symm (FundamentalGroup.fromPath ⟦W.kZeroObjectLoop X⟧)

@[simp] theorem kZeroFundamentalGroupEquiv_objectClass (X : C) :
    W.kZeroFundamentalGroupEquiv (W.kZeroObjectClass X) =
      FundamentalGroup.fromPath ⟦W.kZeroObjectLoop X⟧ :=
  W.kZeroFundamentalGroupEquiv.apply_symm_apply _

@[simp] theorem kZeroObjectClass_zero : W.kZeroObjectClass W.zero = 1 := by
  apply W.kZeroFundamentalGroupEquiv.injective
  rw [map_one, W.kZeroFundamentalGroupEquiv_objectClass, W.kZeroObjectLoop_zero]
  rfl

end CategoryTheory.Waldhausen.Structure
