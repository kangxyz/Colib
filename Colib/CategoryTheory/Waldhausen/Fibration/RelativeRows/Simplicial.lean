/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.SplitFiberZero
public import Colib.KTheory.Waldhausen.Functoriality
public import Colib.KTheory.Waldhausen.ZeroFunctor

/-! # The original inner S-constructions of relative quotient rows

This is the actual outer simplicial diagram of inner S-constructions, with
its actual tail projection and constant split-fiber inclusion. The common
object/hom universe is explicit, as required by the existing raw S-map API.
No realization equivalence or homotopy-fiber conclusion is assumed here.


Implementation provenance:
`Quillen/Waldhausen/Fibration/RelativeRows/Simplicial.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.RelativeRows

/-- Equal original exact functors induce the same original S-map. -/
theorem sSetMap_eq_of_functor_eq {C D : Type u} [Category.{u} C] [Category.{u} D]
    {V : Structure C} {W : Structure D} {F G : C ⥤ D}
    (hF : IsExact V.cof V.weq W.cof W.weq F)
    (hG : IsExact V.cof V.weq W.cof W.weq G) (h : F = G) :
    sSetMap hF = sSetMap hG := by subst G; rfl

variable {C : Type u} [Category.{u} C]

/-- The actual inner S-construction of each ordinary quotient-row category. -/
def ordinarySRows (W : Structure C) : SimplexCategoryᵒᵖ ⥤ SSet.{u} where
  obj n := sSet (QuotientRows.waldhausenStructure W n.unop).cof
    (QuotientRows.waldhausenStructure W n.unop).weq
  map α := sSetMap (QuotientRows.reindex_exact W α.unop)
  map_id n := (sSetMap_eq_of_functor_eq (QuotientRows.reindex_exact W (𝟙 n.unop))
    (IsExact.id _ _) (QuotientRows.reindex_id W n.unop)).trans (sSetMap_id _)
  map_comp α β := (sSetMap_eq_of_functor_eq
    (QuotientRows.reindex_exact W (β.unop ≫ α.unop))
    ((QuotientRows.reindex_exact W α.unop).comp (QuotientRows.reindex_exact W β.unop))
    (QuotientRows.reindex_comp W β.unop α.unop)).trans (sSetMap_comp_sSetMap _ _).symm

variable {V : Structure C} (N : NestedWeakEquivalences V)

/-- The actual inner S-construction of every actual relative row category. -/
def relativeSRows : SimplexCategoryᵒᵖ ⥤ SSet.{u} where
  obj n := sSet (waldhausenStructure N n.unop).cof (waldhausenStructure N n.unop).weq
  map α := sSetMap (reindex_exact N α.unop)
  map_id n := (sSetMap_eq_of_functor_eq (reindex_exact N (𝟙 n.unop))
    (IsExact.id _ _) (reindex_id N n.unop)).trans (sSetMap_id _)
  map_comp α β := (sSetMap_eq_of_functor_eq
    (reindex_exact N (β.unop ≫ α.unop))
    ((reindex_exact N α.unop).comp (reindex_exact N β.unop))
    (reindex_comp N β.unop α.unop)).trans (sSetMap_comp_sSetMap _ _).symm

/-- The original strictly outer-natural acyclic-tail projection. -/
def tailSRows : relativeSRows N ⟶ ordinarySRows (acyclicStructure N) where
  app n := sSetMap (tailFunctor_exact N n.unop)
  naturality n m α := by
    change sSetMap (reindex_exact N α.unop) ≫ sSetMap (tailFunctor_exact N m.unop) =
      sSetMap (tailFunctor_exact N n.unop) ≫ sSetMap (QuotientRows.reindex_exact
          (acyclicStructure N) α.unop)
    rw [sSetMap_comp_sSetMap, sSetMap_comp_sSetMap]

/-- The original strictly outer-natural split-fiber inclusion. -/
def fiberSRows : (Functor.const SimplexCategoryᵒᵖ).obj (sSet V.cof V.weq) ⟶ relativeSRows N where
  app n := sSetMap (fiber_exact N n.unop)
  naturality n m α := by
    change 𝟙 _ ≫ sSetMap (fiber_exact N m.unop) =
      sSetMap (fiber_exact N n.unop) ≫ sSetMap (reindex_exact N α.unop)
    rw [Category.id_comp, sSetMap_comp_sSetMap]
    exact sSetMap_eq_of_functor_eq _ _ (fiber_reindex N α.unop).symm

/-- Original row restriction preserves the actual constant zero functor strictly. -/
theorem zeroFunctor_reindex {D : Type u} [Category.{u} D] (W : Structure D) {m n :
    SimplexCategory} (α : m ⟶ n) :
    zeroFunctor (C := C) (QuotientRows.waldhausenStructure W n) ⋙ QuotientRows.reindex W α =
      zeroFunctor (C := C) (QuotientRows.waldhausenStructure W m) := by
  refine CategoryTheory.Functor.ext (fun _ ↦ QuotientRows.reindex_zero W α) ?_
  intro X Y f
  simp [zeroFunctor]

/-- The genuine constant-zero section into the ordinary row S-constructions. -/
def zeroSRows {D : Type u} [Category.{u} D] (W : Structure D) :
    (Functor.const SimplexCategoryᵒᵖ).obj (sSet V.cof V.weq) ⟶ ordinarySRows W where
  app n := sSetMap (zeroFunctor_isExact V (QuotientRows.waldhausenStructure W n.unop))
  naturality n m α := by
    change 𝟙 _ ≫ sSetMap (zeroFunctor_isExact V (QuotientRows.waldhausenStructure W m.unop)) =
      sSetMap (zeroFunctor_isExact V (QuotientRows.waldhausenStructure W n.unop)) ≫
        sSetMap (QuotientRows.reindex_exact W α.unop)
    rw [Category.id_comp, sSetMap_comp_sSetMap]

/-- The original split inclusion followed by the original tail is exactly the constant-zero section.
-/
@[simp] theorem fiberSRows_tailSRows : fiberSRows N ≫ tailSRows N = zeroSRows (V := V)
    (acyclicStructure N) := by
  apply NatTrans.ext
  funext n
  change sSetMap (fiber_exact N n.unop) ≫ sSetMap (tailFunctor_exact N n.unop) = _
  rw [sSetMap_comp_sSetMap]
  exact sSetMap_eq_of_functor_eq ((fiber_exact N n.unop).comp (tailFunctor_exact N n.unop))
    (zeroFunctor_isExact V (QuotientRows.waldhausenStructure (acyclicStructure N) n.unop))
    (fiber_tail N n.unop)

/-- The original relative S-map is literal postcomposition on every inner simplex. -/
@[simp] theorem relativeSRows_map_val {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n)
    (k : SimplexCategoryᵒᵖ) (X : ((relativeSRows N).obj m).obj k) :
    (((relativeSRows N).map α).app k X).val = X.val ⋙ reindex N α.unop := rfl

/-- The original tail S-map retains the original quotient diagrams and transformations. -/
@[simp] theorem tailSRows_app_val (n k : SimplexCategoryᵒᵖ)
    (X : ((relativeSRows N).obj n).obj k) :
    (((tailSRows N).app n).app k X).val = X.val ⋙ tailFunctor N n.unop := rfl

/-- The original split S-map retains the literal zero-tail inclusion. -/
@[simp] theorem fiberSRows_app_hom_val (n k : SimplexCategoryᵒᵖ) (X : (sSet V.cof V.weq).obj k) :
    (TypeCat.Hom.hom (X := (sSet V.cof V.weq).obj k)
      (Y := (sSet (waldhausenStructure N n.unop).cof
        (waldhausenStructure N n.unop).weq).obj k) (((fiberSRows N).app n).app k) X).val =
      X.val ⋙ fiber N n.unop := rfl


end CategoryTheory.Waldhausen.Fibration.RelativeRows
