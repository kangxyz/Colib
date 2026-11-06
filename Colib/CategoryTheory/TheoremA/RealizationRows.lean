/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.CoproductHomotopy
public import Colib.CategoryTheory.TheoremA.SimplicialReplacement
public import Mathlib.Topology.Category.TopCat.Limits.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Homotopy.Contractible

/-! Source: Quillen/CategoryTheory/TheoremA/RealizationRows.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps and universal properties retained. -/

/-!
# Realization of the rows of a simplicial replacement

The coproduct of a family of simplicial sets realizes to the topological
disjoint union of their realizations. In particular, a family of actual
homotopy equivalences gives an actual homotopy equivalence on each row of
the simplicial replacement. The forward map is the canonical induced map.

This is the rowwise step only. Passing from rowwise homotopy equivalences
to the realization of a bisimplicial set requires a separate gluing theorem.
-/
@[expose] public section

noncomputable section

open SSet CategoryTheory Limits Opposite
open scoped Simplicial Topology unitInterval

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.TheoremA

variable {ι : Type u}

/-- The realization of a replacement row is the disjoint union of the
realizations of its fibers over all base chains. -/
def replacementRowRealizationIso {D : Type u} [SmallCategory D]
    (H : D ⥤ SSet.{u}) (p : SimplexCategoryᵒᵖ) :
    |replacementRow H p| ≅ TopCat.of (Σ s : (nerve D).obj p, |H.obj (s.obj 0)|) :=
  SSet.realizationSigmaIso fun s : (nerve D).obj p ↦ H.obj (s.obj 0)

/-- Objectwise homotopy equivalences give actual homotopy equivalences on
all realized replacement rows. No natural choice of inverse is required. -/
def replacementRowRealizationHomotopyEquiv {D : Type u} [SmallCategory D]
    {H K : D ⥤ SSet.{u}}
    (e : ∀ d, ContinuousMap.HomotopyEquiv |H.obj d| |K.obj d|)
    (p : SimplexCategoryᵒᵖ) :
    ContinuousMap.HomotopyEquiv |replacementRow H p| |replacementRow K p| :=
  SSet.realizationSigmaHomotopyEquiv fun s : (nerve D).obj p ↦ e (s.obj 0)

/-- For a natural transformation whose component realizations are homotopy
 equivalences, the canonical row map is the forward map of the row equivalence. -/
theorem replacementRowRealizationHomotopyEquiv_toFun
    {D : Type u} [SmallCategory D] {H K : D ⥤ SSet.{u}} (η : H ⟶ K)
    (e : ∀ d, ContinuousMap.HomotopyEquiv |H.obj d| |K.obj d|)
    (he : ∀ d, (e d).toFun = (SSet.toTop.map (η.app d)).hom)
    (p : SimplexCategoryᵒᵖ) :
    (replacementRowRealizationHomotopyEquiv e p).toFun =
      (SSet.toTop.map (replacementRowNatMap η p)).hom :=
  SSet.realizationSigmaHomotopyEquiv_toFun
    (fun s : (nerve D).obj p ↦ η.app (s.obj 0))
    (fun s : (nerve D).obj p ↦ e (s.obj 0))
    (fun s : (nerve D).obj p ↦ he (s.obj 0))

/-- The unique diagram map to the point simplicial set. -/
def replacementPointAugmentation {D : Type u} [SmallCategory D]
    (H : D ⥤ SSet.{u}) : H ⟶ (Functor.const D).obj (Δ[0] : SSet.{u}) where
  app d := SSet.stdSimplex.isTerminalObj₀.from (H.obj d)
  naturality _ _ _ := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- Contractible fibers give actual homotopy equivalences on the realized
rows of the canonical augmentation to the constant point diagram. -/
def contractibleReplacementRowHomotopyEquiv {D : Type u} [SmallCategory D]
    (H : D ⥤ SSet.{u}) (h : ∀ d, ContractibleSpace |H.obj d|)
    (p : SimplexCategoryᵒᵖ) :
    ContinuousMap.HomotopyEquiv |replacementRow H p|
      |replacementRow ((Functor.const D).obj (Δ[0] : SSet.{u})) p| :=
  replacementRowRealizationHomotopyEquiv (fun d ↦ by
    letI := h d
    exact (ContractibleSpace.hequiv |H.obj d| |(Δ[0] : SSet.{u})|).some) p

/-- The contractible-row equivalence realizes the canonical augmentation,
not an unspecified equivalence of the same two spaces. -/
theorem contractibleReplacementRowHomotopyEquiv_toFun
    {D : Type u} [SmallCategory D]
    (H : D ⥤ SSet.{u}) (h : ∀ d, ContractibleSpace |H.obj d|)
    (p : SimplexCategoryᵒᵖ) :
    (contractibleReplacementRowHomotopyEquiv H h p).toFun =
      (SSet.toTop.map (replacementRowNatMap (replacementPointAugmentation H) p)).hom := by
  apply replacementRowRealizationHomotopyEquiv_toFun
  intro d
  apply ContinuousMap.ext
  intro x
  exact @Subsingleton.elim |(Δ[0] : SSet.{u})| inferInstance _ _

end CategoryTheory.TheoremA
