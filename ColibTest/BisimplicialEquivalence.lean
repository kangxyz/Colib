/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.Topology.Realization.BisimplicialEquivalence
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.TheoremA SSet SSet.BisimplicialRealization
open scoped Simplicial Topology
universe u
variable {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y)

example (h : ∀ n, SSet.IsRealizationEquivalence (η.app (op ⦋n⦌))) :
    SSet.IsRealizationEquivalence (diagonalMap η) :=
  diagonalMap_isRealizationEquivalence η h

example (h : ∀ n, SSet.IsRealizationEquivalence (η.app (op ⦋n⦌))) (n : ℕ) :
    SSet.IsRealizationEquivalence (stageMap η n) :=
  stageMap_isRealizationEquivalence η h n

example (h : ∀ n, SSet.IsRealizationEquivalence (η.app (op ⦋n⦌))) (n : ℕ) :
    SSet.IsRealizationEquivalence (latchingMap η n) :=
  latchingMap_isRealizationEquivalence η h n

example (n : ℕ) : IsPushout (attachmentToStage X n) (attachment X n).ι
    (stageInclusion X n) (rowToStage X n) := attachment_isPushout X n

example : IsColimit (stageCocone X) := stageCoconeIsColimit X

variable
  (e : ∀ n, ContinuousMap.HomotopyEquiv |X.obj (op ⦋n⦌)| |Y.obj (op ⦋n⦌)|)
  (he : ∀ n, (e n).toFun = (SSet.toTop.map (η.app (op ⦋n⦌))).hom)

example : (diagonalRealizationHomotopyEquiv η e he).toFun =
    (SSet.toTop.map (diagonalMap η)).hom := rfl

example : (iteratedRealizationHomotopyEquiv η e he).toFun =
    (iteratedRealizationMap (Functor.whiskerRight η SSet.toTop)).hom := rfl

example : ContinuousMap.Homotopic
    ((diagonalRealizationHomotopyEquiv η e he).toFun.comp
      (diagonalRealizationHomotopyEquiv η e he).invFun) (ContinuousMap.id _) :=
  (diagonalRealizationHomotopyEquiv η e he).right_inv
