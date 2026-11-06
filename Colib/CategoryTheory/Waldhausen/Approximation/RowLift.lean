/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Rows.InitialRestriction
public import Colib.CategoryTheory.Waldhausen.Approximation.RelativeFlags

/-! # Actual row lifting by initial flags and quotient descent

The given base App2 constructs an actual source flag. Genuine cofiber
completion and fully faithful initial restriction descend the entire strict
factorization to the original quotient rows. The first row map here is not
asserted to be a Reedy cofibration; that is supplied separately by an honest
source row factorization.

Implementation provenance: `Quillen/Waldhausen/Approximation/RowLift.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, hypotheses,
chosen zero objects and universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.Waldhausen.QuotientRows


noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v'
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.QuotientRows
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- The initial flag retains the actual zero vertex and every original map. -/
def initialWeakFlag {n : SimplexCategory} (A : Obj W n) : WeakFlag W.cof W.weq n.len where
  diagram := (initialFlagFunctor W n).obj A
  zero := A.property.zero 0
  cofibration := initialFlag_map_cof W A

variable {n : SimplexCategory} (L : WeakFlag W.cof W.weq n.len)

/-- The original quotient-by-zero projections recover the whole input flag. -/
def completionFlagUnit : L.diagram ⟶
    (initialFlagFunctor W n).obj (completeCofibrationFlag W L.diagram L.cofibration) where
  app i := completionQuotient W L.diagram L.cofibration (interval 0 i (Fin.zero_le _))
  naturality _ _ f :=
    (completionQuotient_comp_map W L.diagram L.cofibration
      ((initialIntervals n).map f)).symm

theorem completionFlagUnit_app_isIso (i : Fin (n.len + 1)) :
    IsIso ((completionFlagUnit W L).app i) := by
  let hzero : IsIso (W.isZero.from_ (L.diagram.obj (interval 0 i (Fin.zero_le _)).val.1)) :=
    L.zero.isIso W.isZero _
  exact (completionQuotient_isPushout W L.diagram L.cofibration
    (interval 0 i (Fin.zero_le _))).isIso_inl_of_isIso

/-- The comparison is an actual natural isomorphism of original flags. -/
def completionFlagIso : L.diagram ≅
    (initialFlagFunctor W n).obj (completeCofibrationFlag W L.diagram L.cofibration) := by
  letI (i : Fin (n.len + 1)) : IsIso ((completionFlagUnit W L).app i) :=
    completionFlagUnit_app_isIso W L i
  exact NatIso.ofComponents (fun i ↦ asIso ((completionFlagUnit W L).app i))
    (fun f ↦ (completionFlagUnit W L).naturality f)

@[simp] theorem completionFlagIso_hom_app (i : Fin (n.len + 1)) :
    (completionFlagIso W L).hom.app i =
      completionQuotient W L.diagram L.cofibration (interval 0 i (Fin.zero_le _)) := rfl

end CategoryTheory.Waldhausen.QuotientRows

namespace CategoryTheory.Waldhausen.HasApproximationProperty
open QuotientRows
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}
  (h : HasApproximationProperty W V F)
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  {n : SimplexCategory} {A : Obj W n} {B : Obj V n}
  (α : (postcompose W V hF n).obj A ⟶ B)

/-- The original initial comparison, with no replacement of its components. -/
def rowInitialComparison : (initialWeakFlag W A).diagram ⋙ F ⟶
    (initialWeakFlag V B).diagram :=
  (initialFlagFunctor V n).map α

/-- The actual source flag produced by the original relative App2 induction. -/
def rowLiftFlag : WeakFlag W.cof W.weq n.len :=
  relativeFlag h hF (initialWeakFlag W A) (initialWeakFlag V B) (rowInitialComparison hF α)

/-- Complete that actual source flag by genuine cofiber squares. -/
def liftedRow : Obj W n :=
  completeCofibrationFlag W (rowLiftFlag h hF α).diagram (rowLiftFlag h hF α).cofibration

/-- Descend the original source flag comparison to the entire original row. -/
def rowLiftInclusion : A ⟶ liftedRow h hF α :=
  extendInitialFlagMap W
    (relativeFlagInclusion h hF (initialWeakFlag W A) (initialWeakFlag V B)
      (rowInitialComparison hF α) ≫ (completionFlagIso W (rowLiftFlag h hF α)).hom)

/-- The entire original target comparison is the actual quotient descendant. -/
def rowLiftProjection : (postcompose W V hF n).obj (liftedRow h hF α) ⟶ B :=
  extendInitialFlagMap V
    (Functor.whiskerRight (completionFlagIso W (rowLiftFlag h hF α)).inv F ≫
      relativeFlagProjection h hF (initialWeakFlag W A) (initialWeakFlag V B)
        (rowInitialComparison hF α))

/-- Genuine quotient gluing proves weakness at every interval of the target row. -/
theorem rowLiftProjection_weak : weq V n (rowLiftProjection h hF α) := by
  apply extendInitialFlagMap_weak
  intro i
  exact V.weq.comp_mem _ _ (V.weq_iso _ inferInstance)
    (relativeFlagProjection_weak h hF (initialWeakFlag W A) (initialWeakFlag V B)
      (rowInitialComparison hF α) i)

/-- The original entire row map factors strictly, not only up to a flag comparison. -/
theorem rowLift_factorization :
    (postcompose W V hF n).map (rowLiftInclusion h hF α) ≫ rowLiftProjection h hF α = α := by
  apply (initialFlagFunctor V n).map_injective
  ext i
  change F.map ((rowLiftInclusion h hF α).hom.app (interval 0 i (Fin.zero_le _))) ≫
    (rowLiftProjection h hF α).hom.app (interval 0 i (Fin.zero_le _)) = _
  simp only [rowLiftInclusion, rowLiftProjection, extendInitialFlagMap,
    ObjectProperty.homMk_hom, extendInitialFlagAt_initial, NatTrans.comp_app,
    Functor.whiskerRight_app, F.map_comp]
  rw [Category.assoc, ← Category.assoc (F.map ((completionFlagIso W (rowLiftFlag h hF
    α)).hom.app i)),
    ← F.map_comp, Iso.hom_inv_id_app, F.map_id, Category.id_comp]
  exact congrArg (fun a ↦ a.app i)
    (relativeFlag_factorization h hF (initialWeakFlag W A) (initialWeakFlag V B)
      (rowInitialComparison hF α))

include h in
/-- Unrestricted factorization through a genuine source row is proved from base App2. -/
theorem exists_rowLift : ∃ (A' : Obj W n) (a : A ⟶ A')
    (p : (postcompose W V hF n).obj A' ⟶ B),
    weq V n p ∧ (postcompose W V hF n).map a ≫ p = α :=
  ⟨liftedRow h hF α, rowLiftInclusion h hF α, rowLiftProjection h hF α,
    rowLiftProjection_weak h hF α, rowLift_factorization h hF α⟩

end CategoryTheory.Waldhausen.HasApproximationProperty
