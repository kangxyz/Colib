/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremA.SkeletalAttachments

/-! Source: Quillen/CategoryTheory/TheoremA/SkeletalNaturality.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Native topology lower owners are reused. -/

/-! # Naturality of the enriched skeletal attachments -/
@[expose] public section

noncomputable section

open SSet TopCat CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial Topology

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.TheoremA

/-- A map in the coefficient variable of an outer product. -/
def outerProductCoefficientMap {K X Y : SSet.{u}} (f : X ⟶ Y) :
    outerProduct K X ⟶ outerProduct K Y where
  app p := {
    app q := ↾fun x ↦ ⟨x.1, f.app q x.2⟩
    naturality q r α := by
      ext x : 3
      exact congrArg (Sigma.mk x.1) (ConcreteCategory.congr_hom (f.naturality α) x.2) }
  naturality _ _ _ := rfl

/-- Maps of coefficients commute strictly with the outer boundary inclusion. -/
theorem outerProductCoefficientMap_naturality {K L X Y : SSet.{u}}
    (f : K ⟶ L) (g : X ⟶ Y) :
    outerProductMap f ≫ outerProductCoefficientMap g =
      outerProductCoefficientMap g ≫ outerProductMap f := rfl

variable {D : Type u} [SmallCategory D] {H K : D ⥤ SSet.{u}} (η : H ⟶ K)

/-- A map of diagrams induces maps on every base restriction. -/
def replacementRestrictionMap (A : (nerve D).Subcomplex) :
    replacementRestriction H A ⟶ replacementRestriction K A where
  app p := {
    app q := ↾fun x ↦ ⟨x.1, (η.app (x.1.1.obj 0)).app q x.2⟩
    naturality q r β := by
      ext x : 3
      exact congrArg (Sigma.mk x.1)
        (ConcreteCategory.congr_hom ((η.app (x.1.1.obj 0)).naturality β) x.2) }
  naturality p q α := by
    ext r x : 4
    apply congrArg (Sigma.mk _)
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (η.naturality (firstVertexEdge α x.1.1)) r) x.2

/-- Naturality extends to the whole skeletal tower. -/
def replacementSkeletonMap : replacementSkeleton H ⟶ replacementSkeleton K where
  app n := replacementRestrictionMap η ((nerve D).skeleton n)
  naturality _ _ _ := rfl

/-- The exhaustive cocones respect the original replacement map. -/
@[reassoc]
theorem replacementSkeletonMap_ι (n : ℕ) :
    (replacementSkeletonMap η).app n ≫ replacementRestrictionι K ((nerve D).skeleton n) =
      replacementRestrictionι H ((nerve D).skeleton n) ≫ simplicialReplacementMap η := rfl

/-- The map of all enriched cell interiors induced by the coefficient map. -/
def replacementCellsMap (n : ℕ) : replacementCells H n ⟶ replacementCells K n :=
  bisimplicialSigmaDesc fun s ↦ outerProductCoefficientMap (η.app (s.1.obj 0)) ≫
    bisimplicialSigmaι (fun s ↦ replacementCell K s) s

/-- The corresponding map of all actual enriched cell boundaries. -/
def replacementCellBoundariesMap (n : ℕ) :
    replacementCellBoundaries H n ⟶ replacementCellBoundaries K n :=
  bisimplicialSigmaDesc fun s ↦ outerProductCoefficientMap (η.app (s.1.obj 0)) ≫
    bisimplicialSigmaι (fun s ↦ replacementCellBoundary K s) s

@[reassoc]
theorem replacementCellsMap_boundary (n : ℕ) :
    replacementCellsBoundaryι H n ≫ replacementCellsMap η n =
      replacementCellBoundariesMap η n ≫ replacementCellsBoundaryι K n := rfl

/-- Characteristic maps are compatible with arbitrary coefficient maps. -/
@[reassoc]
theorem replacementCellsMap_characteristic (n : ℕ) :
    replacementCellsCharacteristic H n ≫ (replacementSkeletonMap η).app (n + 1) =
      replacementCellsMap η n ≫ replacementCellsCharacteristic K n := by
  ext p q x : 5
  apply congrArg (Sigma.mk _)
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (η.naturality (firstVertexEdge x.2.1.down.op x.1.1)) q) x.2.2

/-- Attaching maps are compatible with arbitrary coefficient maps. -/
@[reassoc]
theorem replacementCellsMap_attaching (n : ℕ) :
    replacementCellsAttaching H n ≫ (replacementSkeletonMap η).app n =
      replacementCellBoundariesMap η n ≫ replacementCellsAttaching K n := by
  ext p q x : 5
  apply congrArg (Sigma.mk _)
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (η.naturality (firstVertexEdge x.2.1.1.down.op x.1.1)) q) x.2.2

/-- The natural comparison of the actual realized skeletal towers. -/
def realizedReplacementSkeletonMap :
    realizedReplacementSkeleton H ⟶ realizedReplacementSkeleton K :=
  Functor.whiskerRight (replacementSkeletonMap η) (diagonalFunctor ⋙ SSet.toTop)

end CategoryTheory.TheoremA
