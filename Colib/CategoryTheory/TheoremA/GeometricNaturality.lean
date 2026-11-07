/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.TheoremA.GeometricAttachments
public import Colib.CategoryTheory.TheoremA.SkeletalEquivalences

/-!
Adapted from `Quillen/CategoryTheory/TheoremA/GeometricNaturality.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps.

# Diagram maps in the original geometric attachment coordinates

The actual enriched-cell coordinate homeomorphisms identify the map induced by
a diagram transformation with its original fiber map times the identity of the
geometric simplex or boundary. The parameter map preserves every original
nondegenerate base-chain label.
-/

@[expose] public section
noncomputable section
open SSet TopCat _root_.stdSimplex
open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.TheoremA

/-- Original enriched simplex coordinates are natural in the fiber map. -/
theorem realizedEnrichedCellHomeomorph_naturality {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ)
    (x : |diagonalSSet (outerProduct (Δ[n] : SSet.{u}) X)|) :
    realizedEnrichedCellHomeomorph Y n
        (SSet.toTop.map (diagonalMap (outerProductCoefficientMap (K := (Δ[n] : SSet.{u})) f)) x) =
      (SSet.toTop.map f (realizedEnrichedCellHomeomorph X n x).1,
        (realizedEnrichedCellHomeomorph X n x).2) := by
  have hdiag := ConcreteCategory.congr_hom
    (congrArg SSet.toTop.map (diagonalOuterProductIso_coefficient (B := (Δ[n] : SSet.{u})) f)) x
  simp only [Functor.map_comp, ConcreteCategory.comp_apply] at hdiag
  change realizationProductSimplexParameterHomeomorph Y n
      (SSet.toTop.map (diagonalOuterProductIso Δ[n] Y).hom
        (SSet.toTop.map
          (diagonalMap (outerProductCoefficientMap (K := (Δ[n] : SSet.{u})) f)) x)) = _
  rw [hdiag]
  exact congrArg
    (fun z : |Y| × |(Δ[n] : SSet.{u})| ↦ (z.1, SimplexCategory.toTopHomeo ⦋n⦌ z.2))
    (ConcreteCategory.congr_hom
      (prodComparison_natural_whiskerRight SSet.toTop (B := (Δ[n] : SSet.{u})) f)
      (SSet.toTop.map (diagonalOuterProductIso Δ[n] X).hom x))

/-- Original enriched boundary coordinates are natural in the fiber map. -/
theorem realizedEnrichedBoundaryHomeomorph_naturality {X Y : SSet.{u}} (f : X ⟶ Y) (n : ℕ)
    (x : |diagonalSSet (outerProduct (∂Δ[n] : SSet.{u}) X)|) :
    realizedEnrichedBoundaryHomeomorph Y n
        (SSet.toTop.map (diagonalMap (outerProductCoefficientMap (K := (∂Δ[n] : SSet.{u})) f)) x) =
      (SSet.toTop.map f (realizedEnrichedBoundaryHomeomorph X n x).1,
        (realizedEnrichedBoundaryHomeomorph X n x).2) := by
  have hdiag := ConcreteCategory.congr_hom
    (congrArg SSet.toTop.map (diagonalOuterProductIso_coefficient (B := (∂Δ[n] : SSet.{u})) f)) x
  simp only [Functor.map_comp, ConcreteCategory.comp_apply] at hdiag
  change realizationProductBoundaryHomeomorph Y n
      (SSet.toTop.map (diagonalOuterProductIso (∂Δ[n] : SSet.{u}) Y).hom
        (SSet.toTop.map
          (diagonalMap (outerProductCoefficientMap (K := (∂Δ[n] : SSet.{u})) f)) x)) = _
  rw [hdiag]
  exact congrArg
    (fun z : |Y| × |(∂Δ[n] : SSet.{u})| ↦ (z.1, realizationBoundaryHomeomorph n z.2))
    (ConcreteCategory.congr_hom
      (prodComparison_natural_whiskerRight SSet.toTop (B := (∂Δ[n] : SSet.{u})) f)
      (SSet.toTop.map (diagonalOuterProductIso (∂Δ[n] : SSet.{u}) X).hom x))

/-- The original realized coproduct map on an included summand. -/
@[simp]
theorem realizedBisimplicialSigmaMap_inclusion {ι : Type u}
    {X Y : ι → SimplexCategoryᵒᵖ ⥤ SSet.{u}} (f : ∀ i, X i ⟶ Y i)
    (i : ι) (x : |diagonalSSet (X i)|) :
    SSet.toTop.map (diagonalMap (bisimplicialSigmaMap f))
        (SSet.toTop.map (diagonalMap (bisimplicialSigmaι X i)) x) =
      SSet.toTop.map (diagonalMap (bisimplicialSigmaι Y i))
        (SSet.toTop.map (diagonalMap (f i)) x) := by
  have h := congrArg (diagonalFunctor ⋙ SSet.toTop).map
    (bisimplicialSigmaι_map f i)
  simp only [Functor.map_comp] at h
  exact ConcreteCategory.congr_hom h x

variable {D : Type u} [SmallCategory D] {H K : D ⥤ SSet.{u}}

/-- The original disjoint-union parameter map induced by a diagram transformation. -/
def replacementCellParametersMap (η : H ⟶ K) (n : ℕ) :
    C(replacementCellParameters H n, replacementCellParameters K n) :=
  ContinuousMap.sigmaContinuousMap fun s : (nerve D).nonDegenerate n ↦
    (SSet.toTop.map (η.app (s.val.obj 0))).hom

/-- The original family cell map becomes the parameter map times the simplex identity. -/
theorem realizedReplacementCellsHomeomorph_naturality (η : H ⟶ K) (n : ℕ)
    (x : |diagonalSSet (replacementCells H n)|) :
    realizedReplacementCellsHomeomorph K n
        (SSet.toTop.map (diagonalMap (replacementCellsMap η n)) x) =
      (replacementCellParametersMap η n (realizedReplacementCellsHomeomorph H n x).1,
        (realizedReplacementCellsHomeomorph H n x).2) := by
  obtain ⟨⟨s, y⟩, rfl⟩ :=
    (TopCat.homeoOfIso (realizedDiagonalSigmaIso
      (fun s : (nerve D).nonDegenerate n ↦ replacementCell H s))).symm.surjective x
  have hi : (TopCat.homeoOfIso (realizedDiagonalSigmaIso
      (fun s : (nerve D).nonDegenerate n ↦ replacementCell H s))).symm ⟨s, y⟩ =
      SSet.toTop.map (diagonalMap (bisimplicialSigmaι (fun s ↦ replacementCell H s) s)) y :=
    realizedDiagonalSigmaIso_inv_apply _ _ _
  rw [hi]
  rw [show replacementCellsMap η n = bisimplicialSigmaMap
    (fun s : (nerve D).nonDegenerate n ↦
      (outerProductCoefficientMap (η.app (s.val.obj 0)) :
        replacementCell H s ⟶ replacementCell K s))
    from rfl]
  refine (congrArg (realizedReplacementCellsHomeomorph K n)
    (realizedBisimplicialSigmaMap_inclusion
      (X := fun s ↦ replacementCell H s) (Y := fun s ↦ replacementCell K s)
      (fun s : (nerve D).nonDegenerate n ↦
        outerProductCoefficientMap (η.app (s.val.obj 0))) s y)).trans ?_
  rw [realizedReplacementCellsHomeomorph_inclusion, realizedReplacementCellsHomeomorph_inclusion]
  exact congrArg (fun z : |K.obj (s.val.obj 0)| × _root_.stdSimplex ℝ (Fin (n + 1)) ↦
    ((⟨s, z.1⟩ : replacementCellParameters K n), z.2))
      (realizedEnrichedCellHomeomorph_naturality (η.app (s.val.obj 0)) n y)

/-- The original family boundary map becomes the parameter map times the boundary identity. -/
theorem realizedReplacementBoundariesHomeomorph_naturality (η : H ⟶ K) (n : ℕ)
    (x : |diagonalSSet (replacementCellBoundaries H n)|) :
    realizedReplacementBoundariesHomeomorph K n
        (SSet.toTop.map (diagonalMap (replacementCellBoundariesMap η n)) x) =
      (replacementCellParametersMap η n (realizedReplacementBoundariesHomeomorph H n x).1,
        (realizedReplacementBoundariesHomeomorph H n x).2) := by
  obtain ⟨⟨s, y⟩, rfl⟩ :=
    (TopCat.homeoOfIso (realizedDiagonalSigmaIso
      (fun s : (nerve D).nonDegenerate n ↦ replacementCellBoundary H s))).symm.surjective x
  have hi : (TopCat.homeoOfIso (realizedDiagonalSigmaIso
      (fun s : (nerve D).nonDegenerate n ↦ replacementCellBoundary H s))).symm ⟨s, y⟩ =
      SSet.toTop.map (diagonalMap (bisimplicialSigmaι (fun s ↦ replacementCellBoundary H s) s)) y :=
    realizedDiagonalSigmaIso_inv_apply _ _ _
  rw [hi]
  rw [show replacementCellBoundariesMap η n = bisimplicialSigmaMap
    (fun s : (nerve D).nonDegenerate n ↦
      (outerProductCoefficientMap (η.app (s.val.obj 0)) :
        replacementCellBoundary H s ⟶ replacementCellBoundary K s))
    from rfl]
  refine (congrArg (realizedReplacementBoundariesHomeomorph K n)
    (realizedBisimplicialSigmaMap_inclusion
      (X := fun s ↦ replacementCellBoundary H s) (Y := fun s ↦ replacementCellBoundary K s)
      (fun s : (nerve D).nonDegenerate n ↦
        outerProductCoefficientMap (η.app (s.val.obj 0))) s y)).trans ?_
  rw [realizedReplacementBoundariesHomeomorph_inclusion,
    realizedReplacementBoundariesHomeomorph_inclusion]
  exact congrArg (fun z : |K.obj (s.val.obj 0)| × _root_.stdSimplex.boundary n ↦
    ((⟨s, z.1⟩ : replacementCellParameters K n), z.2))
      (realizedEnrichedBoundaryHomeomorph_naturality (η.app (s.val.obj 0)) n y)

end CategoryTheory.TheoremA
