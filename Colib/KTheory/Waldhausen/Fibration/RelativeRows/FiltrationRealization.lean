/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Fibration.RelativeRows.FiltrationNerves
public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.Simplicial
public import Colib.Topology.Realization.BisimplicialEquivalence

/-! # The original relative S-realization and genuine mixed cofibration rows

Both original row directions and the nerve direction are kept. The actual
original-grid presentation and the proved initial-filtration equivalences
give the forward comparison. Its total map is natural before realization;
no naturality of chosen cofiber inverses is assumed.


Implementation provenance:
`Quillen/Waldhausen/Fibration/RelativeRows/FiltrationRealization.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.RelativeRows
section Diagrams
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)

/-- The relative ordinal direction restricts the original initial chains. -/
def innerFiltrationReindex {n n' : SimplexCategory} (α : n' ⟶ n) :
    innerFiltrationNerve N n ⟶ innerFiltrationNerve N n' where
  app m := nerveMap (MixedNerves.fineWeakCofReindex (RowWeakEquivalences.nested N m.unop) α)
  naturality m m' β := by
    ext k F : 4
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The actual three-direction target, with relative degree as its first coordinate. -/
def innerFiltrationRows : SimplexCategoryᵒᵖ ⥤ (SimplexCategoryᵒᵖ ⥤ SSet.{max u v}) where
  obj n := innerFiltrationNerve N n.unop
  map α := innerFiltrationReindex N α.unop
  map_id _ := by
    ext m k F : 5
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl)
  map_comp _ _ := by
    ext m k F : 5
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- Take only the two original inner diagonal indices, leaving relative degree intact. -/
def relativeFiltrationDiagonals : SimplexCategoryᵒᵖ ⥤ SSet.{max u v} :=
  innerFiltrationRows N ⋙ SSet.diagonalFunctor

/-- On the full diagonal both orders use literally the same three original indices. -/
def relativeFiltrationTotalIso : SSet.diagonalSSet (relativeFiltrationDiagonals N) ≅
    SSet.diagonalSSet (MixedNerves.cofRowDiagonals N) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro n m α
    ext F : 3
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl))

@[simp] theorem relativeFiltrationTotalIso_hom_app (n : SimplexCategoryᵒᵖ)
    (F : (SSet.diagonalSSet (relativeFiltrationDiagonals N)).obj n) :
    (relativeFiltrationTotalIso N).hom.app n F = F := rfl
end Diagrams

section Realization
variable {C : Type u} [SmallCategory C] {V : Structure C}
  (N : NestedWeakEquivalences V) (he : ExtensionAxiom N.coarse)

/-- The actual original S-grid is first presented as weak rows, then read as its initial
filtration. -/
def relativeFiltrationSSet (n : SimplexCategory) :
    (relativeSRows N).obj (op n) ⟶ (relativeFiltrationDiagonals N).obj (op n) :=
  (QuotientRows.sSetWeakRowDiagonalIso (waldhausenStructure N n)).hom ≫
    SSet.diagonalMap (innerFiltrationNerveMap N he n)

/-- Actual degreewise realization equivalence with the original grid/filtration map forward. -/
def relativeFiltrationHomotopyEquiv (n : SimplexCategory) :
    ContinuousMap.HomotopyEquiv |(relativeSRows N).obj (op n)|
      |(relativeFiltrationDiagonals N).obj (op n)| :=
  (TopCat.homeoOfIso (SSet.toTop.mapIso
    (QuotientRows.sSetWeakRowDiagonalIso (waldhausenStructure N n)))).toHomotopyEquiv.trans
    (SSet.BisimplicialRealization.diagonalRealizationHomotopyEquiv (innerFiltrationNerveMap N he n)
      (fun m ↦ innerSFiltrationClassifyingHomotopyEquiv N he ⦋m⦌ n) (fun _ ↦ rfl))

@[simp] theorem relativeFiltrationHomotopyEquiv_toFun (n : SimplexCategory) :
    (relativeFiltrationHomotopyEquiv N he n).toFun =
      (SSet.toTop.map (relativeFiltrationSSet N he n)).hom := by
  simp only [relativeFiltrationHomotopyEquiv, relativeFiltrationSSet, Functor.map_comp]
  rfl

/-- The unchanged original forward comparison is strictly natural in relative degree. -/
def relativeFiltrationMap : relativeSRows N ⟶ relativeFiltrationDiagonals N where
  app n := relativeFiltrationSSet N he n.unop
  naturality n n' α := by
    ext k F : 4
    apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The original total relative grid-to-filtration map, with only the literal diagonal identity. -/
def relativeFiltrationTotalMap : SSet.diagonalSSet (relativeSRows N) ⟶
    SSet.diagonalSSet (MixedNerves.cofRowDiagonals N) :=
  SSet.diagonalMap (relativeFiltrationMap N he) ≫ (relativeFiltrationTotalIso N).hom

/-- The original total relative S-construction genuinely realizes to the mixed cofibration model. -/
def relativeFiltrationTotalHomotopyEquiv :
    ContinuousMap.HomotopyEquiv |SSet.diagonalSSet (relativeSRows N)|
      |SSet.diagonalSSet (MixedNerves.cofRowDiagonals N)| :=
  (SSet.BisimplicialRealization.diagonalRealizationHomotopyEquiv (relativeFiltrationMap N he)
    (fun n ↦ relativeFiltrationHomotopyEquiv N he ⦋n⦌)
    (fun n ↦ relativeFiltrationHomotopyEquiv_toFun N he ⦋n⦌)).trans
    (TopCat.homeoOfIso (SSet.toTop.mapIso (relativeFiltrationTotalIso N))).toHomotopyEquiv

/-- The genuine total equivalence retains the exact original forward map. -/
@[simp] theorem relativeFiltrationTotalHomotopyEquiv_toFun :
    (relativeFiltrationTotalHomotopyEquiv N he).toFun =
      (SSet.toTop.map (relativeFiltrationTotalMap N he)).hom := by
  simp only [relativeFiltrationTotalHomotopyEquiv, relativeFiltrationTotalMap, Functor.map_comp]
  rfl

end Realization
end CategoryTheory.Waldhausen.Fibration.RelativeRows
