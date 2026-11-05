/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.AlgebraicTopology.SimplicialSet.MixedOrdinalContraction
public import Colib.AlgebraicTopology.SimplicialSet.MixedOrdinalFunctor
public import Colib.AlgebraicTopology.SimplicialSet.OrdinalSubdivisionBisimplicial


/-! # The outer mixed cylinder of a bisimplicial set

Only the outer ordinal is enlarged. The inner (nerve) degree stays unchanged.
The minimum-cut contraction is an explicit homotopy on the actual diagonal.
-/
/-! Implementation provenance: extracted from
`Quillen/Topology/Realization/MixedOrdinalBisimplicial.lean`
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps, proofs,
assumptions, and universes are retained; only namespaces/imports are migrated.
-/
@[expose] public section

noncomputable section
open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SSet.MixedOrdinalCylinder

/-- Apply the mixed cylinder in the outer simplicial direction only. -/
def outerCylinder (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) : SimplexCategoryᵒᵖ ⥤ SSet.{u} :=
  (X.flip ⋙ cylinderFunctor).flip

@[simp] theorem outerCylinder_obj_obj (X : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    (n m : SimplexCategoryᵒᵖ) :
    ((outerCylinder X).obj n).obj m =
      (Σ φ : Cut n.unop, (X.obj (op (mixedOrdinal φ))).obj m) := rfl

/-- Outer first-copy restriction, keeping the inner degree unchanged. -/
def outerProjection (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) : outerCylinder X ⟶ X :=
  (flipFunctor _ _ _).map (Functor.whiskerLeft X.flip projectionNatTrans)

/-- The zero-cut inclusion in the outer direction. -/
def outerZeroSection (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) : X ⟶ outerCylinder X :=
  (flipFunctor _ _ _).map (Functor.whiskerLeft X.flip zeroSectionNatTrans)

/-- The one-cut inclusion of ordinary outer subdivision. -/
def outerOneSection (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    OrdinalSubdivision.δ.op ⋙ X ⟶ outerCylinder X :=
  (flipFunctor _ _ _).map (Functor.whiskerLeft X.flip oneSectionNatTrans)

@[simp] theorem outerZeroSection_projection (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    outerZeroSection X ≫ outerProjection X = 𝟙 X := by
  ext n m x
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (zeroSection_projection (X.flip.obj m)) n) x

@[simp] theorem outerOneSection_projection (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    outerOneSection X ≫ outerProjection X = OrdinalSubdivision.horizontalEndpoint X := by
  ext n m x
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (oneSection_projection (X.flip.obj m)) n) x

/-- Lowering the cut commutes with maps of the underlying simplex data. -/
theorem map_lowerSimplex {X Y : SSet.{u}} (f : X ⟶ Y)
    {n : SimplexCategory} (s : Simplex X n) (τ : Cut n) :
    (map f).app (op n) (lowerSimplex X s τ) = lowerSimplex Y ((map f).app (op n) s) τ := by
  rcases s with ⟨φ, x⟩
  change (⟨minCut φ τ, f.app _ (X.map _ x)⟩ : Simplex Y n) =
    ⟨minCut φ τ, Y.map _ (f.app _ x)⟩
  congr 1
  exact ConcreteCategory.congr_hom (f.naturality _) x

/-- The minimum-cut homotopy on the diagonal changes only the outer ordinal. -/
def outerContractionCylinder (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    SSet.diagonalSSet (outerCylinder X) ⊗ Δ[1] ⟶ SSet.diagonalSSet (outerCylinder X) where
  app n := ↾fun z ↦ lowerSimplex (X.flip.obj n) z.1 z.2.down
  naturality n m α := by
    apply ConcreteCategory.hom_ext
    intro z
    change lowerSimplex (X.flip.obj m)
      ((map (X.flip.map α)).app m (reindex (X.flip.obj n) α.unop z.1))
      (α.unop ≫ z.2.down) =
        (map (X.flip.map α)).app m (reindex (X.flip.obj n) α.unop
          (lowerSimplex (X.flip.obj n) z.1 z.2.down))
    rw [lowerSimplex_naturality, map_lowerSimplex]

/-- The actual diagonal contraction from zero-section/projection to identity. -/
def outerContraction (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    SSet.Homotopy
      (SSet.diagonalMap (outerProjection X) ≫ SSet.diagonalMap (outerZeroSection X)) (𝟙
        _) where
  h := outerContractionCylinder X
  h₀ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    exact lowerSimplex_zero (X.flip.obj n) s
  h₁ := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    exact lowerSimplex_one (X.flip.obj n) s
  rel := by ext n z; exact z.1.property.elim

end SSet.MixedOrdinalCylinder
