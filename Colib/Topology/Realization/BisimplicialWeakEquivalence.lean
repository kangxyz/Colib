/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.BisimplicialEquivalence
public import Colib.Topology.Realization.BisimplicialWeakLatching
public import Colib.Topology.Realization.SequentialWeakEquivalence
/-!
# Rowwise complete weakness on the original diagonal realization

Weak latching comparisons propagate through actual outer skeletal pushouts.
Sequential closed-embedding compact support then proves complete weakness
of the original diagonal map. Components, degree zero and empty rows are
included; no row homotopy inverse or Whitehead theorem is an input.

Implementation provenance:
`Quillen/Topology/Realization/BisimplicialWeakEquivalence.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses and universe parameters are retained.
-/
@[expose] public section


noncomputable section
open Topology TopCat SSet
open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SSet.BisimplicialRealization
open CategoryTheory.TheoremA
variable {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y)

/-- The attaching subcomplex inherits every rowwise equivalence. -/
theorem attachmentMap_isRealizationWeakEquivalence
    (h : ∀ n, IsRealizationWeakEquivalence (η.app (op ⦋n⦌))) (n : ℕ) :
    IsRealizationWeakEquivalence (attachmentMap n η) := by
  let : CompactSpace |(Δ[n] : SSet.{u})| := (SimplexCategory.toTopHomeo ⦋n⦌).symm.compactSpace
  let : T2Space |(Δ[n] : SSet.{u})| := (SimplexCategory.toTopHomeo ⦋n⦌).symm.t2Space
  have hmono (Z : SimplicialObject SSet.{u}) :
      Mono ((latching Z n).ι ▷ (∂Δ[n] : SSet.{u})) := by
    rw [NatTrans.mono_iff_mono_app]
    intro q
    apply (CategoryTheory.mono_iff_injective _).2
    intro x y hxy
    change (x.1.val, x.2) = (y.1.val, y.2) at hxy
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj hxy
    exact Prod.ext (Subtype.ext h₁) h₂
  have := hmono X
  have := hmono Y
  have hl := latchingMap_isRealizationWeakEquivalence η h n
  exact IsRealizationWeakEquivalence.pushout
    (attachment_union_isPushout X n) (attachment_union_isPushout Y n)
    (latchingMap η n ▷ (∂Δ[n] : SSet.{u})) (η.app (op ⦋n⦌) ▷ (∂Δ[n] : SSet.{u}))
    (latchingMap η n ▷ (Δ[n] : SSet.{u})) (attachmentMap n η)
    (by rw [← comp_whiskerRight, ← comp_whiskerRight, latchingMap_ι])
    (by exact whisker_exchange _ _)
    (attachmentMap_boundary n η).symm (attachmentMap_latching n η).symm
    (hl.whiskerRight _) ((h n).whiskerRight _) (hl.whiskerRight _)

/-- Rowwise realization equivalences give equivalences on every finite outer skeleton. -/
theorem stageMap_isRealizationWeakEquivalence
    (h : ∀ n, IsRealizationWeakEquivalence (η.app (op ⦋n⦌))) (n : ℕ) :
    IsRealizationWeakEquivalence (stageMap η n) := by
  induction n with
  | zero =>
    exact IsRealizationWeakEquivalence.of_isInitial _ (stageZeroIsInitial X)
      (stageZeroIsInitial Y)
  | succ n ih =>
    let : CompactSpace |(Δ[n] : SSet.{u})| := (SimplexCategory.toTopHomeo ⦋n⦌).symm.compactSpace
    let : T2Space |(Δ[n] : SSet.{u})| := (SimplexCategory.toTopHomeo ⦋n⦌).symm.t2Space
    exact IsRealizationWeakEquivalence.pushout
      (attachment_isPushout X n).flip (attachment_isPushout Y n).flip
      (attachmentMap n η) (η.app (op ⦋n⦌) ▷ (Δ[n] : SSet.{u})) (stageMap η n)
      (stageMap η (n + 1))
      (attachmentMap_ι n η).symm (attachmentMap_toStage n η).symm
      (rowToStage_naturality n η).symm (stageInclusion_naturality n η).symm
      (attachmentMap_isRealizationWeakEquivalence η h n) ((h n).whiskerRight _) ih

/-- Complete rowwise weak equivalences give complete weakness of the original
realized diagonal map, with no continuous row inverses chosen. -/
theorem diagonalMap_isRealizationWeakEquivalence
    (h : ∀ n, IsRealizationWeakEquivalence (η.app (op ⦋n⦌))) :
    IsRealizationWeakEquivalence (diagonalMap η) := by
  let A := stageDiagram X ⋙ SSet.toTop
  let B := stageDiagram Y ⋙ SSet.toTop
  let α : A ⟶ B := Functor.whiskerRight (stageDiagramMap η) SSet.toTop
  let c : Cocone A := SSet.toTop.mapCocone (stageCocone X)
  let d : Cocone B := SSet.toTop.mapCocone (stageCocone Y)
  have hc : IsColimit c := isColimitOfPreserves SSet.toTop (stageCoconeIsColimit X)
  have hd : IsColimit d := isColimitOfPreserves SSet.toTop (stageCoconeIsColimit Y)
  have hmono (Z : SimplicialObject SSet.{u}) (n : ℕ) :
      Mono ((stageDiagram Z).map (homOfLE (Nat.le_succ n))) := by
    change Mono (SSet.Subcomplex.homOfLE ((outerSkeleton Z).monotone (Nat.le_succ n)))
    infer_instance
  let (n : ℕ) : T1Space (A.obj n) := inferInstanceAs (T1Space |stage X n|)
  let (n : ℕ) : T1Space (B.obj n) := inferInstanceAs (T1Space |stage Y n|)
  have hA (n : ℕ) : Topology.IsClosedEmbedding (A.map (homOfLE (Nat.le_succ n))) := by
    have := hmono X n
    exact realization_mono_isClosedEmbedding _
  have hB (n : ℕ) : Topology.IsClosedEmbedding (B.map (homOfLE (Nat.le_succ n))) := by
    have := hmono Y n
    exact realization_mono_isClosedEmbedding _
  have hw := TopCat.SequentialColimit.colimitMap_isWeakHomotopyEquivalence α c hc d hd hA hB
    (stageMap_isRealizationWeakEquivalence η h)
  have he : hc.map d α = SSet.toTop.map (diagonalMap η) := by
    apply hc.hom_ext
    intro n
    rw [hc.ι_map]
    change SSet.toTop.map (stageMap η n) ≫ SSet.toTop.map (outerSkeleton Y n).ι =
      SSet.toTop.map (outerSkeleton X n).ι ≫ SSet.toTop.map (diagonalMap η)
    simpa only [Functor.map_comp] using congrArg SSet.toTop.map (stageMap_ι η n)
  rw [he] at hw
  exact hw

end SSet.BisimplicialRealization
