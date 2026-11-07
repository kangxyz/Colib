/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Category.TopCat.SequentialColimit.PathHomotopy

public import Colib.Topology.Category.TopCat.SequentialColimit.Groupoid
public import Colib.Topology.ClassifyingSpace.NerveCompletion.NerveStageTower

/-!
# Nerve Homotopy Reflection

The actual original nerve tower, restricted to stages starting at three.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopCat SSet
open TopCat.SimplexAttachment
universe u v
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover
open TopCat.SimplexAttachment
open stdSimplex.Boundary
open FundamentalGroupoid.SequentialColimit
attribute [local instance] Localization.groupoid

/-- The actual original nerve tower, restricted to stages starting at three. -/
def nerveDecoderTower (C : Type u) [Category.{v} C] : ℕ ⥤ TopCat.{max u v} :=
  (show Monotone (fun n : ℕ => n + 3) from
    fun _ _ h => Nat.add_le_add_right h 3).functor ⋙ realizedSkeletonTower (nerve C)

/-- Restriction transports across every finite interval of original nerve stages. -/
def nerveStageComparison (C : Type u) [Category.{v} C] {k n : ℕ} (h : k ≤ n) :
    FundamentalGroupoid.map ((nerveDecoderTower C).map (homOfLE h)).hom ⋙
      nerveStageDecoder C n ≅ nerveStageDecoder C k :=
  stageComparison (F := nerveDecoderTower C) (nerveStageDecoder C) (nerveStageStepIso C) h

/-- Ambient homotopy of two actual finite-stage paths forces equality of their
constructed decoder values. The proof factors the compact homotopy through a
later ORIGINAL stage and composes the proved restriction transports. No full
realization decoder, retraction or faithfulness is assumed. -/
theorem nerveStage_value_of_homotopic (C : Type u) [Category.{v} C] (k : ℕ)
    {x y : nerveFiniteStage C (k + 3)} (p q : Path x y)
    (H : (p.map ((realizedSkeletonCocone (nerve C)).ι.app (k + 3)).hom.continuous).Homotopic
      (q.map ((realizedSkeletonCocone (nerve C)).ι.app (k + 3)).hom.continuous)) :
    (nerveStageDecoder C k).map (Path.Homotopic.Quotient.mk p) =
      (nerveStageDecoder C k).map (Path.Homotopic.Quotient.mk q) := by
  obtain ⟨n, h, Hn⟩ := TopCat.SequentialColimit.path_homotopic_factors
    (realizedSkeletonIsColimit (nerve C))
    (realizedRelativeSkeleton_closedEmbeddings (NerveGraphData.emptyMap C)) (k + 3) p q H
  have hn : 3 ≤ n := by omega
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
  have hn' : n = m + 3 := by omega
  clear hm
  subst n
  have hkm : k ≤ m := by omega
  apply decoder_value_eq_of_later (F := nerveDecoderTower C)
    (nerveStageDecoder C) (nerveStageStepIso C) hkm p q
  have hclass : Path.Homotopic.Quotient.mk
      (p.map ((realizedSkeletonTower (nerve C)).map (homOfLE h)).hom.continuous) =
      Path.Homotopic.Quotient.mk
        (q.map ((realizedSkeletonTower (nerve C)).map (homOfLE h)).hom.continuous) :=
    _root_.Quotient.sound Hn
  change (nerveStageDecoder C m).map (Path.Homotopic.Quotient.mk
      (p.map ((realizedSkeletonTower (nerve C)).map (homOfLE h)).hom.continuous)) =
    (nerveStageDecoder C m).map (Path.Homotopic.Quotient.mk
      (q.map ((realizedSkeletonTower (nerve C)).map (homOfLE h)).hom.continuous))
  exact congrArg (fun f => (nerveStageDecoder C m).map f) hclass

end CategoryTheory.NerveCompletion
