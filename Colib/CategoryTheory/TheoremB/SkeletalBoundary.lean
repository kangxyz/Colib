/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.CartesianProducts
public import Colib.Topology.HomotopyPullback.CoproductAssembly
public import Colib.Topology.Realization.FiniteCompact
public import Colib.Topology.Realization.FiniteHausdorff

/-! # Actual replacement-stage cartesian cube assembly -/
/-! Implementation source: the incoming boundary-to-cell comparison in
`Quillen/CategoryTheory/TheoremB/SkeletalCartesianAssembly.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. This proves this actual incoming face
without transition hypotheses. The attaching face and outgoing cube remain separate. -/
@[expose] public section

open SSet Topology.HomotopyPullback


noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial Topology unitInterval
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.TheoremA

/-- The unique simplex in each degree of the zero-simplex, used to identify point-valued
replacement stages with their base stages. -/
local instance pointSimplexUniqueAssembly (p : SimplexCategoryᵒᵖ) :
    Unique ((Δ[0] : SSet.{u}).obj p) :=
  (SSet.stdSimplex.objEquiv (n := ⦋0⦌) (m := p)).unique

/-- The point coefficient leaves exactly the prescribed simplicial domain. -/
def pointOuterIso (K : SSet.{u}) :
    diagonalSSet (outerProduct K (Δ[0] : SSet.{u})) ≅ K :=
  NatIso.ofComponents (fun p ↦ Equiv.toIso
    { toFun := fun x ↦ x.1
      invFun := fun a ↦ ⟨a, (default : (Δ[0] : SSet.{u}).obj p)⟩
      left_inv := fun x ↦ by
        rcases x with ⟨i, x⟩
        exact congrArg (Sigma.mk i)
          (@Subsingleton.elim ((Δ[0] : SSet.{u}).obj p) inferInstance _ _)
      right_inv := fun _ ↦ rfl }) (by intros; rfl)

/-- The homeomorphism from the realization of the diagonal outer product of `K` with the
zero-simplex to the realization of `K`. -/
abbrev pointOuterHomeomorph (K : SSet.{u}) :
    |diagonalSSet (outerProduct K (Δ[0] : SSet.{u}))| ≃ₜ |K| :=
  TopCat.homeoOfIso (SSet.toTop.mapIso (pointOuterIso K))

/-- Realization of an actual bisimplicial coproduct, with its actual injections. -/
abbrev realizedCofan {ι : Type u} (X : ι → SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    Cofan (fun i ↦ (diagonalFunctor ⋙ SSet.toTop).obj (X i)) :=
  Cofan.mk ((diagonalFunctor ⋙ SSet.toTop).obj (bisimplicialSigma X))
    (fun i ↦ (diagonalFunctor ⋙ SSet.toTop).map (bisimplicialSigmaι X i))

/-- Realization preserves the exact componentwise square of an outer product. -/
theorem pointOuter_square {K L X : SSet.{u}} (k : K ⟶ L)
    (f : X ⟶ (Δ[0] : SSet.{u})) :
    (diagonalFunctor ⋙ SSet.toTop).map (outerProductMap (X := X) k) ≫
      (diagonalFunctor ⋙ SSet.toTop).map (outerProductCoefficientMap f) =
    (diagonalFunctor ⋙ SSet.toTop).map (outerProductCoefficientMap f) ≫
      (diagonalFunctor ⋙ SSet.toTop).map (outerProductMap (X := (Δ[0] : SSet.{u})) k) := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

/-- Boundary product squares are cartesian for every coefficient, even when
its augmentation to a point is not an equivalence. -/
theorem pointOuter_cartesian {K L X : SSet.{u}}
    [LocallyCompactSpace |K|] [LocallyCompactSpace |L|]
    (k : K ⟶ L) (f : X ⟶ (Δ[0] : SSet.{u})) :
    Cartesian ((diagonalFunctor ⋙ SSet.toTop).map (outerProductCoefficientMap (K := K) f)).hom
      ((diagonalFunctor ⋙ SSet.toTop).map (outerProductCoefficientMap (K := L) f)).hom
      ((diagonalFunctor ⋙ SSet.toTop).map (outerProductMap (X := X) k)).hom
      ((diagonalFunctor ⋙ SSet.toTop).map (outerProductMap (X := (Δ[0] : SSet.{u})) k)).hom
      (congrArg TopCat.Hom.hom (pointOuter_square k f)) := by
  apply cartesianOfCoordinates _ _ _ _ _
    (SSet.toTop.map (outerProjection K X)).hom
    (SSet.toTop.map (outerProjection L X)).hom
    (SSet.toTop.map (enrichedMap k (𝟙 X))).hom (SSet.toTop.map k).hom
    (congrArg TopCat.Hom.hom (realizedEnrichedMap_square k (𝟙 X)))
    (Homeomorph.refl _) (Homeomorph.refl _)
    (pointOuterHomeomorph K) (pointOuterHomeomorph L)
  · change (SSet.toTop.map (outerProjection K X)).hom =
      (SSet.toTop.map (diagonalMap (outerProductCoefficientMap f)) ≫
        SSet.toTop.map (pointOuterIso K).hom).hom
    rw [← Functor.map_comp]
    rfl
  · change (SSet.toTop.map (outerProjection L X)).hom =
      (SSet.toTop.map (diagonalMap (outerProductCoefficientMap f)) ≫
        SSet.toTop.map (pointOuterIso L).hom).hom
    rw [← Functor.map_comp]
    rfl
  · rfl
  · change (SSet.toTop.map (pointOuterIso K).hom ≫ SSet.toTop.map k).hom =
      (SSet.toTop.map (diagonalMap (outerProductMap k)) ≫ SSet.toTop.map (pointOuterIso L).hom).hom
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  · exact enrichedMap_cartesian k (𝟙 X) (Homeomorph.refl |X|).toHomotopyEquiv
      (by rw [CategoryTheory.Functor.map_id]; rfl)

variable {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})

/-- The actual coefficient map commutes with the realized cell-boundary inclusions. -/
theorem realizedReplacementCellsMap_boundary {J : D ⥤ SSet.{u}} (η : H ⟶ J) (n : ℕ) :
    (diagonalFunctor ⋙ SSet.toTop).map (replacementCellsBoundaryι H n) ≫
      (diagonalFunctor ⋙ SSet.toTop).map (replacementCellsMap η n) =
    (diagonalFunctor ⋙ SSet.toTop).map (replacementCellBoundariesMap η n) ≫
      (diagonalFunctor ⋙ SSet.toTop).map (replacementCellsBoundaryι J n) := by
  rw [← Functor.map_comp, ← Functor.map_comp, replacementCellsMap_boundary]

/-- The incoming boundary-to-cell face of the actual successor cube. -/
theorem replacementBoundary_cartesian (n : ℕ) :
    Cartesian ((diagonalFunctor ⋙ SSet.toTop).map
      (replacementCellBoundariesMap (replacementPointAugmentation H) n)).hom
      ((diagonalFunctor ⋙ SSet.toTop).map
        (replacementCellsMap (replacementPointAugmentation H) n)).hom
      ((diagonalFunctor ⋙ SSet.toTop).map (replacementCellsBoundaryι H n)).hom
        ((diagonalFunctor ⋙ SSet.toTop).map (replacementCellsBoundaryι ((Functor.const D).obj
        (Δ[0] : SSet.{u})) n)).hom
      (congrArg TopCat.Hom.hom (realizedReplacementCellsMap_boundary H
        (replacementPointAugmentation H) n)) := by
  let : CompactSpace |(Δ[n] : SSet.{u})| := (SimplexCategory.toTopHomeo ⦋n⦌).symm.compactSpace
  let : T2Space |(Δ[n] : SSet.{u})| := (SimplexCategory.toTopHomeo ⦋n⦌).symm.t2Space
  apply cartesianCofan
    (fun s : (nerve D).nonDegenerate n ↦ (diagonalFunctor ⋙ SSet.toTop).obj
      (replacementCellBoundary H s))
    (fun s : (nerve D).nonDegenerate n ↦ (diagonalFunctor ⋙ SSet.toTop).obj (replacementCell H s))
    (fun s : (nerve D).nonDegenerate n ↦ (diagonalFunctor ⋙ SSet.toTop).obj (replacementCellBoundary
      ((Functor.const D).obj (Δ[0] : SSet.{u})) s))
    (fun s : (nerve D).nonDegenerate n ↦ (diagonalFunctor ⋙ SSet.toTop).obj (replacementCell
      ((Functor.const D).obj (Δ[0] : SSet.{u})) s))
    (realizedCofan (replacementCellBoundary H)) (realizedCofan (replacementCell H))
    (realizedCofan (replacementCellBoundary ((Functor.const D).obj (Δ[0] : SSet.{u}))))
      (realizedCofan (replacementCell
      ((Functor.const D).obj (Δ[0] : SSet.{u}))))
    (realizedBisimplicialSigmaIsColimit _) (realizedBisimplicialSigmaIsColimit _)
    (realizedBisimplicialSigmaIsColimit _) (realizedBisimplicialSigmaIsColimit _)
    ((diagonalFunctor ⋙ SSet.toTop).map
      (replacementCellBoundariesMap (replacementPointAugmentation H) n))
    ((diagonalFunctor ⋙ SSet.toTop).map
        (replacementCellsMap (replacementPointAugmentation H) n))
    ((diagonalFunctor ⋙ SSet.toTop).map (replacementCellsBoundaryι H n)) ((diagonalFunctor ⋙
      SSet.toTop).map (replacementCellsBoundaryι ((Functor.const D).obj (Δ[0] : SSet.{u})) n))
    (realizedReplacementCellsMap_boundary H (replacementPointAugmentation H) n)
    (fun s ↦ (diagonalFunctor ⋙ SSet.toTop).map (outerProductCoefficientMap
      (K := (∂Δ[n] : SSet.{u})) ((replacementPointAugmentation H).app (s.1.obj 0))))
    (fun s ↦ (diagonalFunctor ⋙ SSet.toTop).map (outerProductCoefficientMap
      (K := (Δ[n] : SSet.{u})) ((replacementPointAugmentation H).app (s.1.obj 0))))
    (fun s ↦ (diagonalFunctor ⋙ SSet.toTop).map (replacementCellBoundaryι H s))
    (fun s ↦ (diagonalFunctor ⋙ SSet.toTop).map (replacementCellBoundaryι ((Functor.const
      D).obj (Δ[0] : SSet.{u})) s))
    (fun s ↦ pointOuter_square ∂Δ[n].ι ((replacementPointAugmentation H).app (s.1.obj 0)))
  · intro s
    change (diagonalFunctor ⋙ SSet.toTop).map _ ≫ (diagonalFunctor ⋙ SSet.toTop).map _ =
      (diagonalFunctor ⋙ SSet.toTop).map _ ≫ (diagonalFunctor ⋙ SSet.toTop).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  · intro s
    change (diagonalFunctor ⋙ SSet.toTop).map _ ≫ (diagonalFunctor ⋙ SSet.toTop).map _ =
      (diagonalFunctor ⋙ SSet.toTop).map _ ≫ (diagonalFunctor ⋙ SSet.toTop).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  · intro s
    change (diagonalFunctor ⋙ SSet.toTop).map _ ≫ (diagonalFunctor ⋙ SSet.toTop).map _ =
      (diagonalFunctor ⋙ SSet.toTop).map _ ≫ (diagonalFunctor ⋙ SSet.toTop).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  · intro s
    change (diagonalFunctor ⋙ SSet.toTop).map _ ≫ (diagonalFunctor ⋙ SSet.toTop).map _ =
      (diagonalFunctor ⋙ SSet.toTop).map _ ≫ (diagonalFunctor ⋙ SSet.toTop).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  · intro s
    exact pointOuter_cartesian ∂Δ[n].ι ((replacementPointAugmentation H).app (s.1.obj 0))


end CategoryTheory.TheoremA
