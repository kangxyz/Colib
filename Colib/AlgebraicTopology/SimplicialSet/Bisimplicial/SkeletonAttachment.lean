/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.AlgebraicTopology.SimplicialSet.Bisimplicial.Skeleton
public import Colib.AlgebraicTopology.SimplicialSet.Bisimplicial.Latching

/-! Implementation provenance: adapted from
`Quillen/Topology/Realization/BisimplicialSkeletonAttachment.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The native simplicial objects,
realization maps and full proof are retained. -/

/-!
# Full-row outer skeletal attachments

Every successor outer skeleton is obtained by attaching the full coefficient
row times the standard simplex, along the union of its latching cylinder and
its boundary cylinder. This is a genuine pushout of simplicial sets.
-/
@[expose] public section


noncomputable section
open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SSet.BisimplicialRealization
open CategoryTheory.TheoremA

variable (X : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ)

/-- The full-row attaching subcomplex `(X_n × ∂Δ[n]) ∪ (L_n X × Δ[n])`. -/
def attachment : (X.obj (op ⦋n⦌) ⊗ (Δ[n] : SSet.{u})).Subcomplex :=
  (latching X n).unionProd ∂Δ[n]

/-- The attaching subcomplex is precisely the pullback of the preceding
outer skeleton under row evaluation. -/
lemma preimage_outerSkeleton :
    (outerSkeleton X n).preimage (diagonalEvaluation X ⦋n⦌) = attachment X n := by
  ext q ⟨x, f⟩
  change (X.map f.down.op).app q x ∈ (outerSkeleton X n).obj q ↔ _
  rw [mem_outerSkeleton_iff_column]
  change (column X q).map f.down.op x ∈ ((column X q).skeleton n).obj q ↔ _
  rw [map_mem_skeleton_iff]
  dsimp only [attachment]
  rw [SSet.Subcomplex.mem_unionProd_iff, mem_latching_iff_degenerate]
  rw [SimplexCategory.epi_iff_surjective]
  change x ∈ (column X q).degenerate n ∨ ¬ Function.Surjective f.down.toOrderHom ↔
    ¬ Function.Surjective f.down.toOrderHom ∨ x ∈ (column X q).degenerate n
  exact or_comm

/-- The canonical attaching map to the preceding stage. -/
def attachmentToStage : (attachment X n : SSet.{u}) ⟶ stage X n :=
  SSet.Subcomplex.lift ((attachment X n).ι ≫ diagonalEvaluation X ⦋n⦌) (by
    rintro q _ ⟨x, rfl⟩
    exact (preimage_outerSkeleton X n).symm.le q x.property)

@[reassoc (attr := simp)]
lemma attachmentToStage_ι :
    attachmentToStage X n ≫ (outerSkeleton X n).ι =
      (attachment X n).ι ≫ diagonalEvaluation X ⦋n⦌ := rfl

/-- Evaluation of the full coefficient row lands in the next skeleton. -/
def rowToStage : X.obj (op ⦋n⦌) ⊗ (Δ[n] : SSet.{u}) ⟶ stage X (n + 1) :=
  SSet.Subcomplex.lift (diagonalEvaluation X ⦋n⦌) (by
    rw [outerSkeleton_succ]
    exact le_sup_right)

@[reassoc (attr := simp)]
lemma rowToStage_ι : rowToStage X n ≫ (outerSkeleton X (n + 1)).ι =
    diagonalEvaluation X ⦋n⦌ := rfl

/-- The inclusion of successive outer skeletons. -/
abbrev stageInclusion : stage X n ⟶ stage X (n + 1) :=
  SSet.Subcomplex.homOfLE ((outerSkeleton X).monotone (Nat.le_succ n))

@[reassoc]
lemma attachment_w : attachmentToStage X n ≫ stageInclusion X n =
    (attachment X n).ι ≫ rowToStage X n := by
  rw [← cancel_mono (outerSkeleton X (n + 1)).ι]
  simp

/-- The skeletal attaching square is also a pullback. -/
lemma attachment_isPullback : IsPullback (attachmentToStage X n)
    (attachment X n).ι (stageInclusion X n) (rowToStage X n) where
  w := attachment_w X n
  isLimit' := ⟨evaluationJointlyReflectsLimits _ (fun q ↦ by
    refine (isLimitMapConePullbackConeEquiv _ _).2 (IsPullback.isLimit ?_)
    rw [Types.isPullback_iff]
    refine ⟨NatTrans.congr_app (attachment_w X n) q, ?_, ?_⟩
    · intro x y h
      exact Subtype.ext h.2
    · intro x y h
      have hval : (diagonalEvaluation X ⦋n⦌).app q y = x.val :=
        (congrArg Subtype.val h).symm
      have hy : y ∈ (attachment X n).obj q := by
        rw [← preimage_outerSkeleton]
        change (diagonalEvaluation X ⦋n⦌).app q y ∈ (outerSkeleton X n).obj q
        rw [hval]
        exact x.property
      exact ⟨⟨y, hy⟩, Subtype.ext hval, rfl⟩)⟩

lemma stage_range_union (q : SimplexCategoryᵒᵖ) :
    Set.range ((stageInclusion X n).app q) ∪
      Set.range ((rowToStage X n).app q) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx := (outerSkeleton_succ X n).le q x.property
  rcases hx with hx | ⟨y, hy⟩
  · exact Or.inl ⟨⟨x.val, hx⟩, Subtype.ext rfl⟩
  · exact Or.inr ⟨y, Subtype.ext hy⟩

/-- Outside the attaching subcomplex, the coefficient is outer nondegenerate
and the simplex operator is surjective. -/
lemma notMem_attachment {q : SimplexCategoryᵒᵖ}
    (x : (X.obj (op ⦋n⦌) ⊗ (Δ[n] : SSet.{u})).obj q)
    (hx : x ∉ (attachment X n).obj q) :
    x.1 ∈ (column X q).nonDegenerate n ∧ Epi x.2.down := by
  rw [attachment, SSet.Subcomplex.mem_unionProd_iff, mem_latching_iff_degenerate] at hx
  rw [not_or] at hx
  refine ⟨hx.2, ?_⟩
  rw [SimplexCategory.epi_iff_surjective]
  exact not_not.mp hx.1

/-- Eilenberg–Zilber uniqueness gives injectivity away from the attachment. -/
lemma rowToStage_injective_off_attachment {q : SimplexCategoryᵒᵖ}
    (x y : (X.obj (op ⦋n⦌) ⊗ (Δ[n] : SSet.{u})).obj q)
    (hx : x ∉ (attachment X n).obj q) (hy : y ∉ (attachment X n).obj q)
    (h : (rowToStage X n).app q x = (rowToStage X n).app q y) : x = y := by
  obtain ⟨hxnd, hxe⟩ := notMem_attachment X n x hx
  obtain ⟨hynd, hye⟩ := notMem_attachment X n y hy
  have := hxe
  have := hye
  have he : (column X q).map x.2.down.op x.1 = (column X q).map y.2.down.op y.1 :=
    congrArg Subtype.val h
  have hxy : x.1 = y.1 := Subtype.ext_iff.mp
    ((column X q).unique_nonDegenerate_simplex _ x.2.down ⟨x.1, hxnd⟩ rfl
      y.2.down ⟨y.1, hynd⟩ he)
  have hmap : x.2.down = y.2.down :=
    (column X q).unique_nonDegenerate_map _ x.2.down ⟨x.1, hxnd⟩ rfl
      y.2.down ⟨y.1, hynd⟩ he
  exact Prod.ext hxy (ULift.ext hmap)

/-- The genuine enriched successor attachment for every bisimplicial set. -/
theorem attachment_isPushout : IsPushout (attachmentToStage X n)
    (attachment X n).ι (stageInclusion X n) (rowToStage X n) where
  w := attachment_w X n
  isColimit' := ⟨evaluationJointlyReflectsColimits _ (fun q ↦ by
    refine (isColimitMapCoconePushoutCoconeEquiv _ _).2 (IsPushout.isColimit ?_)
    refine Types.isPushout_of_isPullback_of_mono' ?_ ?_ ?_
    · exact (attachment_isPullback X n).map ((evaluation _ _).obj q)
    · exact stage_range_union X n q
    · intro x y hx hy h
      apply rowToStage_injective_off_attachment X n x y ?_ ?_ h
      · exact fun hx' ↦ hx ⟨⟨x, hx'⟩, rfl⟩
      · exact fun hy' ↦ hy ⟨⟨y, hy'⟩, rfl⟩)⟩

/-- The attaching object itself is the pushout of the latching and boundary
cylinders over their intersection. -/
theorem attachment_union_isPushout :
    IsPushout ((latching X n).ι ▷ (∂Δ[n] : SSet.{u}))
      ((latching X n : SSet.{u}) ◁ ∂Δ[n].ι)
      (SSet.Subcomplex.unionProd.ι₁ (latching X n) ∂Δ[n])
      (SSet.Subcomplex.unionProd.ι₂ (latching X n) ∂Δ[n]) :=
  SSet.Subcomplex.unionProd.isPushout _ _

section Naturality

variable {X} {Y : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (η : X ⟶ Y)

/-- A bisimplicial map induces the map of enriched attaching subcomplexes. -/
def attachmentMap : (attachment X n : SSet.{u}) ⟶ attachment Y n :=
  SSet.Subcomplex.lift ((attachment X n).ι ≫ (η.app (op ⦋n⦌) ▷ (Δ[n] : SSet.{u}))) (by
    rintro q _ ⟨x, rfl⟩
    have hx := (SSet.Subcomplex.mem_unionProd_iff (latching X n) ∂Δ[n] x.val).1 x.property
    apply (SSet.Subcomplex.mem_unionProd_iff (latching Y n) ∂Δ[n] _).2
    rcases hx with hx | hx
    · exact Or.inl hx
    · apply Or.inr
      have h := ((latchingMap η n).app q ⟨x.val.1, hx⟩).property
      have he := ConcreteCategory.congr_hom (NatTrans.congr_app (latchingMap_ι η n) q)
        ⟨x.val.1, hx⟩
      change ((latchingMap η n).app q ⟨x.val.1, hx⟩).val =
        (η.app (op ⦋n⦌)).app q x.val.1 at he
      change (η.app (op ⦋n⦌)).app q x.val.1 ∈ (latching Y n).obj q
      rw [← he]
      exact h)

@[reassoc (attr := simp)]
lemma attachmentMap_ι : attachmentMap n η ≫ (attachment Y n).ι =
    (attachment X n).ι ≫ (η.app (op ⦋n⦌) ▷ (Δ[n] : SSet.{u})) := rfl

@[reassoc]
lemma attachmentMap_toStage :
    attachmentMap n η ≫ attachmentToStage Y n =
      attachmentToStage X n ≫ stageMap η n := by
  rw [← cancel_mono (outerSkeleton Y n).ι]
  simp only [Category.assoc, attachmentToStage_ι, stageMap_ι]
  rw [← Category.assoc, attachmentMap_ι, Category.assoc,
    diagonalEvaluation_naturality, ← Category.assoc, ← attachmentToStage_ι]
  exact Category.assoc _ _ _

@[reassoc]
lemma rowToStage_naturality :
    (η.app (op ⦋n⦌) ▷ (Δ[n] : SSet.{u})) ≫ rowToStage Y n =
      rowToStage X n ≫ stageMap η (n + 1) := by
  rw [← cancel_mono (outerSkeleton Y (n + 1)).ι]
  simp only [Category.assoc, rowToStage_ι, stageMap_ι]
  rw [← Category.assoc, rowToStage_ι, diagonalEvaluation_naturality]

@[reassoc]
lemma stageInclusion_naturality :
    stageMap η n ≫ stageInclusion Y n = stageInclusion X n ≫ stageMap η (n + 1) := rfl

@[reassoc]
lemma attachmentMap_boundary :
    (η.app (op ⦋n⦌) ▷ (∂Δ[n] : SSet.{u})) ≫
      SSet.Subcomplex.unionProd.ι₁ (latching Y n) ∂Δ[n] =
    SSet.Subcomplex.unionProd.ι₁ (latching X n) ∂Δ[n] ≫ attachmentMap n η := by
  rfl

@[reassoc]
lemma attachmentMap_latching :
    (latchingMap η n ▷ (Δ[n] : SSet.{u})) ≫
      SSet.Subcomplex.unionProd.ι₂ (latching Y n) ∂Δ[n] =
    SSet.Subcomplex.unionProd.ι₂ (latching X n) ∂Δ[n] ≫ attachmentMap n η := by
  ext q x
  apply Subtype.ext
  apply Prod.ext
  · exact ConcreteCategory.congr_hom (NatTrans.congr_app (latchingMap_ι η n) q) x.1
  · rfl

end Naturality

end SSet.BisimplicialRealization
