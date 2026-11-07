/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # Actual term maps in the existing canonical truncation -/
/-! Adapted from
`Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.TruncationMaps`
at pinned Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe v u

namespace CochainComplex

section General

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A] [HasZeroObject A]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (K : HomologicalComplex A c') [∀ i, K.HasHomology i]
  (e : c.Embedding c') [e.IsTruncGE]
  {i : ι} {i' : ι'} (h : e.f i = i')

/-- The canonical projection has its actual boundary opcycle map. -/
@[reassoc]
theorem truncGE_projection_boundary (hi : e.BoundaryGE i) :
    (K.πTruncGE e).f i' ≫ (K.truncGEXIsoOpcycles e h hi).hom = K.pOpcycles i' := by
  rw [HomologicalComplex.πTruncGE, e.liftExtend_f _ _ h,
    K.restrictionToTruncGE'_f_eq_iso_hom_pOpcycles_iso_inv e h hi]
  simp [HomologicalComplex.truncGEXIsoOpcycles]

/-- Away from the boundary, the canonical projection is the chosen term iso. -/
@[reassoc]
theorem truncGE_projection_interior (hi : ¬ e.BoundaryGE i) :
    (K.πTruncGE e).f i' ≫ (K.truncGEXIso e h hi).hom = 𝟙 _ := by
  rw [HomologicalComplex.πTruncGE, e.liftExtend_f _ _ h,
    K.restrictionToTruncGE'_f_eq_iso_hom_iso_inv e h hi]
  simp [HomologicalComplex.truncGEXIso]

end General

variable {A : Type u} [Category.{v} A] [Abelian A] (K : CochainComplex A ℤ)

/-- At the boundary the actual truncation inclusion is the actual cycle inclusion. -/
@[reassoc]
theorem truncLE_inclusion_boundary (n : ℤ) :
    (K.truncLEXIsoCycles n).hom ≫ K.iCycles n = (K.ιTruncLE n).f n := by
  have h := truncGE_projection_boundary K.op (ComplexShape.embeddingUpIntLE n).op
    (i := 0) (i' := n) (by simp) (by
      change (ComplexShape.embeddingUpIntLE n).BoundaryLE 0
      rw [ComplexShape.boundaryLE_embeddingUpIntLE_iff])
  have hh := congrArg (fun f ↦ f ≫ (K.opcyclesOpIso n).hom) h
  rw [show K.op.pOpcycles n ≫ (K.opcyclesOpIso n).hom = (K.iCycles n).op from
    (K.sc n).op_pOpcycles_opcyclesOpIso_hom] at hh
  apply Quiver.Hom.op_inj
  simp only [CochainComplex.truncLEXIsoCycles, HomologicalComplex.truncLEXIsoCycles,
    CochainComplex.ιTruncLE, HomologicalComplex.ιTruncLE]
  simp only [op_comp]
  rw [← hh]
  simp

/-- Below the truncation boundary the actual inclusion is an isomorphism. -/
theorem isIso_truncLE_inclusion_below (n i : ℤ) (hi : i < n) :
    IsIso ((K.ιTruncLE n).f i) := by
  let e := ComplexShape.embeddingUpIntLE n
  let k : ℕ := (n - i).natAbs
  have hk : e.f k = i := by
    dsimp [e, k]
    rw [Int.natAbs_of_nonneg (by omega), sub_sub_cancel]
  have hb : ¬ e.BoundaryLE k := by
    rw [ComplexShape.boundaryLE_embeddingUpIntLE_iff]
    dsimp [k]
    rw [Int.natAbs_eq_zero]
    omega
  let t := K.op.truncGEXIso e.op hk hb
  have h := truncGE_projection_interior K.op e.op hk hb
  have he : (K.op.πTruncGE e.op).f i = t.inv := by
    calc
      _ = ((K.op.πTruncGE e.op).f i ≫ t.hom) ≫ t.inv := by simp
      _ = t.inv := by rw [h, Category.id_comp]
  change IsIso ((K.op.πTruncGE e.op).f i).unop
  rw [he]
  infer_instance

end CochainComplex
