/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremA.RealizationRows
public import Colib.CategoryTheory.TheoremA.IteratedRealization
public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! Source: Quillen/CategoryTheory/TheoremA/RealizationSkeleton.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Native topology lower owners are reused. -/

/-!
# The base-skeleton filtration of a simplicial replacement

Restricting the base chains to subcomplexes of the nerve gives a genuine
filtration of the bisimplicial replacement. The filtration is exhaustive and
is intended for the enriched simplex-attachment presentation.
-/
@[expose] public section

noncomputable section

open SSet TopCat CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial Topology

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.TheoremA

variable {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})

/-- Restrict a replacement row to a subcomplex of its base nerve. -/
def replacementRestrictionRow (A : (nerve D).Subcomplex) (p : SimplexCategoryᵒᵖ) : SSet.{u} :=
  SSet.simplicialSigma fun s : A.obj p ↦ H.obj (s.1.obj 0)

/-- A simplex operator on the base restriction, including the required
covariant transport from the first vertex. -/
def replacementRestrictionRowMap (A : (nerve D).Subcomplex)
    {p q : SimplexCategoryᵒᵖ} (α : p ⟶ q) :
    replacementRestrictionRow H A p ⟶ replacementRestrictionRow H A q where
  app r := ↾fun x ↦ ⟨⟨(nerve D).map α x.1.1, A.map α x.1.2⟩,
    (H.map (firstVertexEdge α x.1.1)).app r x.2⟩
  naturality r s β := by
    ext x : 3
    dsimp [replacementRestrictionRow, SSet.simplicialSigma]
    apply congrArg (Sigma.mk _)
    exact ConcreteCategory.congr_hom ((H.map (firstVertexEdge α x.1.1)).naturality β) x.2

/-- The bisimplicial replacement restricted to a base subcomplex. -/
def replacementRestriction (A : (nerve D).Subcomplex) : SimplexCategoryᵒᵖ ⥤ SSet.{u} where
  obj p := replacementRestrictionRow H A p
  map α := replacementRestrictionRowMap H A α
  map_id p := by
    ext q x : 4
    dsimp [replacementRestrictionRowMap]
    rw [firstVertexEdge_id, H.map_id]
    rfl
  map_comp α β := by
    ext q x : 4
    dsimp [replacementRestrictionRowMap]
    rw [firstVertexEdge_comp, H.map_comp]
    rfl

/-- The canonical inclusion of a base-restricted replacement row. -/
def replacementRestrictionRowι (A : (nerve D).Subcomplex) (p : SimplexCategoryᵒᵖ) :
    replacementRestrictionRow H A p ⟶ replacementRow H p where
  app _ := ↾fun x ↦ ⟨x.1.1, x.2⟩
  naturality _ _ _ := rfl

/-- The canonical inclusion of the base-restricted bisimplicial replacement. -/
def replacementRestrictionι (A : (nerve D).Subcomplex) :
    replacementRestriction H A ⟶ simplicialReplacement H where
  app p := replacementRestrictionRowι H A p
  naturality _ _ _ := rfl

/-- Enlarging a base subcomplex includes the corresponding replacement rows. -/
def replacementRestrictionRowInclusion {A B : (nerve D).Subcomplex}
    (h : A ≤ B) (p : SimplexCategoryᵒᵖ) :
    replacementRestrictionRow H A p ⟶ replacementRestrictionRow H B p where
  app _ := ↾fun x ↦ ⟨⟨x.1.1, h _ x.1.2⟩, x.2⟩
  naturality _ _ _ := rfl

/-- Inclusions between base restrictions are natural in the outer degree. -/
def replacementRestrictionInclusion {A B : (nerve D).Subcomplex} (h : A ≤ B) :
    replacementRestriction H A ⟶ replacementRestriction H B where
  app p := replacementRestrictionRowInclusion H h p
  naturality _ _ _ := rfl

/-- The base-skeleton tower of the actual bisimplicial replacement. -/
def replacementSkeleton : ℕ ⥤ (SimplexCategoryᵒᵖ ⥤ SSet.{u}) where
  obj n := replacementRestriction H ((nerve D).skeleton n)
  map f := replacementRestrictionInclusion H ((nerve D).skeleton.monotone (leOfHom f))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The skeleton inclusions form a cocone with the full replacement as vertex. -/
def replacementSkeletonCocone : Cocone (replacementSkeleton H) where
  pt := simplicialReplacement H
  ι := {
    app n := replacementRestrictionι H ((nerve D).skeleton n)
    naturality _ _ _ := rfl }

/-- The base-skeleton filtration is exhaustive as an actual colimit of
bisimplicial sets, checked independently at every bidegree. -/
def replacementSkeletonIsColimit : IsColimit (replacementSkeletonCocone H) := by
  apply evaluationJointlyReflectsColimits
  intro p
  apply evaluationJointlyReflectsColimits
  intro q
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    refine ⟨p.unop.len + 1, ⟨⟨x.1, (nerve D).mem_skeleton x.1⟩, x.2⟩, ?_⟩
    rfl
  · intro n x y h
    refine ⟨n, 𝟙 n, ?_⟩
    change x = y
    change (⟨x.1.1, x.2⟩ : Σ s : (nerve D).obj p, (H.obj (s.obj 0)).obj q) =
      ⟨y.1.1, y.2⟩ at h
    obtain ⟨hbase, hfiber⟩ := Sigma.ext_iff.mp h
    exact Sigma.ext (Subtype.ext hbase) hfiber

/-- A product with a simplicial set in the outer variable and a simplicial
set in the inner variable, expressed by explicit row coproducts. -/
def outerProduct (K X : SSet.{u}) : SimplexCategoryᵒᵖ ⥤ SSet.{u} where
  obj p := SSet.simplicialSigma fun _ : K.obj p ↦ X
  map α := {
    app := fun _ ↦ ↾fun x ↦ ⟨K.map α x.1, x.2⟩
    naturality := fun _ _ _ ↦ rfl }
  map_id p := by
    ext q x : 4
    dsimp
    simp
  map_comp α β := by
    ext q x : 4
    dsimp
    simp

/-- A map of outer simplicial sets acts on the corresponding outer products. -/
def outerProductMap {K L X : SSet.{u}} (f : K ⟶ L) :
    outerProduct K X ⟶ outerProduct L X where
  app p := {
    app := fun _ ↦ ↾fun x ↦ ⟨f.app p x.1, x.2⟩
    naturality := fun _ _ _ ↦ rfl }
  naturality p q α := by
    ext r x : 4
    apply Sigma.ext
    · exact ConcreteCategory.congr_hom (f.naturality α) x.1
    · rfl

/-- A nondegenerate base simplex as a cell in the canonical skeletal filtration. -/
def replacementBaseCell {n : ℕ} (s : (nerve D).nonDegenerate n) :
    SSet.relativeCellComplexOfMono.Cell
      (SSet.Subcomplex.ι (⊥ : (nerve D).Subcomplex)) n where
  simplex := s.1
  nonDegenerate := s.2
  notMem := by simp

/-- Every proper face (including a degenerate proper face) of a nondegenerate
`n`-simplex belongs to the previous base skeleton. -/
theorem replacementBaseCell_boundary {n : ℕ} (s : (nerve D).nonDegenerate n)
    {p : SimplexCategoryᵒᵖ} (a : (∂Δ[n] : SSet.{u}).obj p) :
    (nerve D).map a.1.down.op s.1 ∈ ((nerve D).skeleton n).obj p := by
  have h := (replacementBaseCell s).preimage_map
  have ha : a.1 ∈ (((SSet.skeletonOfMono
      (SSet.Subcomplex.ι (⊥ : (nerve D).Subcomplex))) n).preimage
      (replacementBaseCell s).map).obj p := by
    rw [h]
    exact a.2
  simpa [SSet.skeletonOfMono, replacementBaseCell,
    SSet.relativeCellComplexOfMono.Cell.map, SSet.yonedaEquiv, uliftYonedaEquiv] using ha

/-- The enriched cell associated to one nondegenerate base simplex. -/
def replacementCell {n : ℕ} (s : (nerve D).nonDegenerate n) :
    SimplexCategoryᵒᵖ ⥤ SSet.{u} :=
  outerProduct Δ[n] (H.obj (s.1.obj 0))

/-- Its actual simplicial boundary in the outer variable. -/
def replacementCellBoundary {n : ℕ} (s : (nerve D).nonDegenerate n) :
    SimplexCategoryᵒᵖ ⥤ SSet.{u} :=
  outerProduct (∂Δ[n] : SSet.{u}) (H.obj (s.1.obj 0))

/-- The enriched boundary inclusion for a single base simplex. -/
def replacementCellBoundaryι {n : ℕ} (s : (nerve D).nonDegenerate n) :
    replacementCellBoundary H s ⟶ replacementCell H s :=
  outerProductMap ∂Δ[n].ι

/-- The characteristic map of an enriched base cell into the next skeleton. -/
def replacementCellCharacteristic {n : ℕ} (s : (nerve D).nonDegenerate n) :
    replacementCell H s ⟶ (replacementSkeleton H).obj (n + 1) where
  app p := {
    app := fun q ↦ ↾fun x ↦
      ⟨⟨(nerve D).map x.1.down.op s.1,
        ((nerve D).skeleton (n + 1)).map x.1.down.op ((nerve D).mem_skeleton s.1)⟩,
        (H.map (firstVertexEdge x.1.down.op s.1)).app q x.2⟩
    naturality := by
      intro q r β
      ext x : 3
      apply congrArg (Sigma.mk _)
      exact ConcreteCategory.congr_hom
        ((H.map (firstVertexEdge x.1.down.op s.1)).naturality β) x.2 }
  naturality p q α := by
    ext r x : 4
    change (⟨⟨(nerve D).map (x.1.down.op ≫ α) s.1, _⟩,
      (H.map (firstVertexEdge (x.1.down.op ≫ α) s.1)).app r x.2⟩ :
        ((replacementSkeleton H).obj (n + 1)).obj q |>.obj r) = _
    rw [firstVertexEdge_comp, H.map_comp]
    rfl

/-- The attaching map takes the actual cell boundary into the preceding skeleton. -/
def replacementCellAttaching {n : ℕ} (s : (nerve D).nonDegenerate n) :
    replacementCellBoundary H s ⟶ (replacementSkeleton H).obj n where
  app p := {
    app := fun q ↦ ↾fun x ↦
      ⟨⟨(nerve D).map x.1.1.down.op s.1, replacementBaseCell_boundary s x.1⟩,
        (H.map (firstVertexEdge x.1.1.down.op s.1)).app q x.2⟩
    naturality := by
      intro q r β
      ext x : 3
      apply congrArg (Sigma.mk _)
      exact ConcreteCategory.congr_hom
        ((H.map (firstVertexEdge x.1.1.down.op s.1)).naturality β) x.2 }
  naturality p q α := by
    ext r x : 4
    change (⟨⟨(nerve D).map (x.1.1.down.op ≫ α) s.1, _⟩,
      (H.map (firstVertexEdge (x.1.1.down.op ≫ α) s.1)).app r x.2⟩ :
        ((replacementSkeleton H).obj n).obj q |>.obj r) = _
    rw [firstVertexEdge_comp, H.map_comp]
    rfl

/-- The enriched characteristic and attaching maps have the required
strict boundary compatibility. -/
theorem replacementCell_square {n : ℕ} (s : (nerve D).nonDegenerate n) :
    replacementCellBoundaryι H s ≫ replacementCellCharacteristic H s =
      replacementCellAttaching H s ≫
        (replacementSkeleton H).map (homOfLE (Nat.le_succ n)) := rfl

end CategoryTheory.TheoremA
