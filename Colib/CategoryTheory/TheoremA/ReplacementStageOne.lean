/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremA.SkeletalNaturality
public import Colib.CategoryTheory.TheoremA.Augmentations
public import Colib.Topology.ClassifyingSpace.ZeroSkeleton
public import Colib.Topology.Realization.Constant

/-! The actual vertex inclusion and first replacement stage, from
`Quillen/CategoryTheory/TheoremB/ReplacementVertex.lean` and
`Quillen/CategoryTheory/TheoremB/ReplacementStageOne.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The existing native constant-nerve-skeleton
lemmas are reused, and the actual stage, coefficients and colimit maps are unchanged. -/
@[expose] public noncomputable section
universe u
open SSet CategoryTheory Limits Opposite
open scoped Simplicial Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.TheoremA
variable {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})

/-- Include a diagram value by the constant base chain at its object. -/
def replacementVertexInclusion (d : D) : H.obj d ⟶ replacementDiagonal H where
  app p := ↾fun x ↦ ⟨(Functor.const (Fin (p.unop.len + 1))).obj d, x⟩
  naturality p q α := by
    ext x : 3
    dsimp [replacementDiagonal, diagonalSSet, simplicialReplacement, replacementRowMap,
      replacementRow, firstVertexEdge]
    simp only [H.map_id]
    rfl

/-- The vertex coproduct includes canonically into the first diagonal base-skeleton. -/
def vertexCoproductToStageOne : SSet.simplicialSigma (fun d : D ↦ H.obj d) ⟶
    diagonalSSet ((replacementSkeleton H).obj 1) where
  app p := ↾fun x ↦ ⟨⟨(Functor.const (Fin (p.unop.len + 1))).obj x.1,
    nerve_constant_mem_zeroSkeleton x.1 p⟩, x.2⟩
  naturality p q α := by
    ext x : 3
    dsimp [diagonalSSet, replacementSkeleton, replacementRestriction,
      replacementRestrictionRowMap, firstVertexEdge, SSet.simplicialSigma]
    simp only [H.map_id]
    rfl

instance vertexCoproductToStageOne_isIso : IsIso (vertexCoproductToStageOne H) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro p
  apply (isIso_iff_bijective _).2
  constructor
  · intro x y hxy
    obtain ⟨hb, hf⟩ := Sigma.ext_iff.mp hxy
    have hbase : x.1 = y.1 := congrArg (fun z ↦ z.1.obj 0) hb
    exact Sigma.ext hbase hf
  · intro z
    refine ⟨⟨z.1.1.obj 0, z.2⟩, ?_⟩
    apply Sigma.ext
    · exact Subtype.ext (nerve_zeroSkeleton_constant z.1.1 z.1.2).symm
    · rfl

/-- Exact simplicial coproduct coordinates for the first base-skeleton. -/
def replacementStageOneIso :
    SSet.simplicialSigma (fun d : D ↦ H.obj d) ≅ diagonalSSet ((replacementSkeleton
      H).obj 1) :=
  asIso (vertexCoproductToStageOne H)

/-- The first stage after realization is the genuine topological coproduct
of the diagram's realized values. -/
def realizedReplacementStageOneHomeomorph :
    (Σ d : D, |H.obj d|) ≃ₜ (realizedReplacementSkeleton H).obj 1 :=
  (TopCat.homeoOfIso (SSet.realizationSigmaIso (fun d : D ↦ H.obj d))).symm.trans
    (TopCat.homeoOfIso (SSet.toTop.mapIso (replacementStageOneIso H)))

/-- The first-stage coproduct inclusion followed by the exhaustive cocone
is precisely the previously constructed vertex inclusion. -/
theorem vertexCoproductToStageOne_ι (d : D) :
    SSet.simplicialSigmaι (fun d : D ↦ H.obj d) d ≫ vertexCoproductToStageOne H ≫
      diagonalMap (replacementRestrictionι H ((nerve D).skeleton 1)) =
        replacementVertexInclusion H d := rfl

/-- The homeomorphism includes each value by its actual realized simplicial map. -/
theorem realizedReplacementStageOneHomeomorph_apply (d : D) (x : |H.obj d|) :
    realizedReplacementStageOneHomeomorph H ⟨d, x⟩ =
      SSet.toTop.map (SSet.simplicialSigmaι (fun d : D ↦ H.obj d) d ≫
        vertexCoproductToStageOne H) x := by
  change SSet.toTop.map (vertexCoproductToStageOne H)
    ((SSet.realizationSigmaIso (fun d : D ↦ H.obj d)).inv ⟨d, x⟩) = _
  rw [SSet.realizationSigmaIso_inv_apply]
  rw [Functor.map_comp]
  rfl

/-- Coefficient maps retain the discrete object coordinate in stage one. -/
theorem realizedReplacementStageOneHomeomorph_naturality
    {H K : D ⥤ SSet.{u}} (η : H ⟶ K) (d : D) (x : |H.obj d|) :
    (realizedReplacementSkeletonMap η).app 1
      (realizedReplacementStageOneHomeomorph H ⟨d, x⟩) =
      realizedReplacementStageOneHomeomorph K ⟨d, SSet.toTop.map (η.app d) x⟩ := by
  rw [realizedReplacementStageOneHomeomorph_apply, realizedReplacementStageOneHomeomorph_apply]
  change (SSet.toTop.map (SSet.simplicialSigmaι (fun d : D ↦ H.obj d) d ≫
      vertexCoproductToStageOne H) ≫
    SSet.toTop.map (diagonalMap ((replacementSkeletonMap η).app 1))) x =
    (SSet.toTop.map (η.app d) ≫
      SSet.toTop.map (SSet.simplicialSigmaι (fun d : D ↦ K.obj d) d ≫
        vertexCoproductToStageOne K)) x
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

/-- Coproduct coordinates retain the exact canonical vertex inclusion into
full realization. -/
theorem realizedReplacementStageOneHomeomorph_colimit (d : D) (x : |H.obj d|) :
    ((diagonalFunctor ⋙ SSet.toTop).mapCocone (replacementSkeletonCocone H)).ι.app 1
      (realizedReplacementStageOneHomeomorph H ⟨d, x⟩) =
        SSet.toTop.map (replacementVertexInclusion H d) x := by
  rw [realizedReplacementStageOneHomeomorph_apply]
  change (SSet.toTop.map (SSet.simplicialSigmaι (fun d : D ↦ H.obj d) d ≫
    vertexCoproductToStageOne H) ≫
      SSet.toTop.map (diagonalMap (replacementRestrictionι H ((nerve D).skeleton 1)))) x = _
  rw [← Functor.map_comp, Category.assoc, vertexCoproductToStageOne_ι]
  rfl

/-- Every replacement vertex projects to its indexing vertex. -/
theorem replacementVertex_base (d : D) (x : |H.obj d|) :
    SSet.toTop.map (replacementBaseMap H)
      (SSet.toTop.map (replacementVertexInclusion H d) x) = classifyingSpacePoint d := by
  change (SSet.toTop.map (replacementVertexInclusion H d) ≫
    SSet.toTop.map (replacementBaseMap H)) x = _
  rw [← Functor.map_comp]
  exact SSet.realization_const_apply (nerveVertex d) x

end CategoryTheory.TheoremA
