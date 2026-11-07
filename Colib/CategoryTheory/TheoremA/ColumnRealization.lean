/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremA.Columns
public import Colib.Topology.ClassifyingSpace.Contraction

/-! Source: Quillen/CategoryTheory/TheoremA/ColumnRealization.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps and universal properties retained. -/

/-!
# Realized source-column equivalences for Quillen's Theorem A

Every flipped column of the comma replacement maps by a genuine homotopy
equivalence to the discrete simplicial set of source chains. The proof uses
the explicit under-category decomposition and its initial objects.
-/
@[expose] public section

noncomputable section

open SSet CategoryTheory Opposite
open scoped Simplicial

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.TheoremA

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

variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- The initial object contracts each under-category summand to a point. -/
def commaColumnSummandHomotopyEquiv (q : SimplexCategoryᵒᵖ)
    (c : ComposableArrows C q.unop.len) :
    ContinuousMap.HomotopyEquiv
      (ClassifyingSpace (StructuredArrow (F.obj (c.obj (Fin.last q.unop.len))) (𝟭 D)))
      |(Δ[0] : SSet.{u})| := by
  letI : ContractibleSpace
      (ClassifyingSpace (StructuredArrow (F.obj (c.obj (Fin.last q.unop.len))) (𝟭 D))) :=
    classifyingSpace_contractible_of_isInitial
      (StructuredArrow.mkIdInitial (T := 𝟭 D) (Y := F.obj (c.obj (Fin.last q.unop.len))))
  exact (ContractibleSpace.hequiv _ _).some

/-- The canonical column augmentation forgetting its contractible summand. -/
def commaColumnSourceMap (q : SimplexCategoryᵒᵖ) :
    commaColumn F q ⟶ (Functor.const SimplexCategoryᵒᵖ).obj (ComposableArrows C q.unop.len) :=
  (commaColumnIso F q).hom ≫
    SSet.simplicialSigmaMap (fun c : ComposableArrows C q.unop.len ↦
      SSet.stdSimplex.isTerminalObj₀.from
        (nerve (StructuredArrow (F.obj (c.obj (Fin.last q.unop.len))) (𝟭 D)))) ≫
    (pointSigmaIso (ComposableArrows C q.unop.len)).hom

/-- The augmentation component has the explicit source-chain target. -/
@[simp]
theorem commaColumnSourceMap_hom_apply (p q : SimplexCategoryᵒᵖ)
    (x : (commaColumn F q).obj p) :
    (ConcreteCategory.hom ((commaColumnSourceMap F q).app p) :
      TypeCat.Fun ((commaColumn F q).obj p) (ComposableArrows C q.unop.len)) x =
      x.2 ⋙ CostructuredArrow.proj F (x.1.obj 0) := rfl

/-- An actual homotopy equivalence from each realized column to its source-chain set. -/
def commaColumnRealizationHomotopyEquiv (q : SimplexCategoryᵒᵖ) :
    ContinuousMap.HomotopyEquiv |commaColumn F q|
      |(Functor.const SimplexCategoryᵒᵖ).obj (ComposableArrows C q.unop.len)| :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso (commaColumnIso F q))).toHomotopyEquiv.trans
    ((SSet.realizationSigmaHomotopyEquiv (commaColumnSummandHomotopyEquiv F q)).trans
      (TopCat.homeoOfIso (SSet.toTop.mapIso
        (pointSigmaIso (ComposableArrows C q.unop.len)))).toHomotopyEquiv)

/-- The equivalence uses the canonical augmentation as its forward map. -/
theorem commaColumnRealizationHomotopyEquiv_toFun (q : SimplexCategoryᵒᵖ) :
    (commaColumnRealizationHomotopyEquiv F q).toFun =
      (SSet.toTop.map (commaColumnSourceMap F q)).hom := by
  have h := SSet.realizationSigmaHomotopyEquiv_toFun
    (fun c : ComposableArrows C q.unop.len ↦ SSet.stdSimplex.isTerminalObj₀.from
      (nerve (StructuredArrow (F.obj (c.obj (Fin.last q.unop.len))) (𝟭 D))))
    (commaColumnSummandHomotopyEquiv F q)
    (fun c ↦ by ext x; exact Subsingleton.elim _ _)
  change (((SSet.toTop.map (pointSigmaIso (ComposableArrows C q.unop.len)).hom).hom.comp
    (SSet.realizationSigmaHomotopyEquiv (commaColumnSummandHomotopyEquiv F
      q)).toFun).comp
      (SSet.toTop.map (commaColumnIso F q).hom).hom) = _
  rw [h]
  simp only [commaColumnSourceMap, Functor.map_comp, TopCat.hom_comp]

end CategoryTheory.TheoremA
