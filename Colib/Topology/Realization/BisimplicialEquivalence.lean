/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.BisimplicialLatchingEquivalences
public import Colib.AlgebraicTopology.SimplicialSet.Bisimplicial.SkeletonAttachment
public import Colib.Topology.Category.TopCat.SequentialColimit.HomotopyInvariance
public import Colib.CategoryTheory.TheoremA.IteratedRealization
public import Colib.Topology.Realization.FiniteHausdorff

/-! Implementation provenance: adapted from
`Quillen/Topology/Realization/BisimplicialEquivalence.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The native simplicial objects,
realization maps and full proof are retained. -/

/-!
# Rowwise equivalences induce genuine diagonal realization equivalences

For arbitrary bisimplicial sets, a map that realizes to a homotopy equivalence
in every row also realizes to a homotopy equivalence on diagonals. The proof
retains the prescribed diagonal map. It uses finite latching pushouts, full-row
outer skeletal attachments, actual monomorphism HEP, and sequential gluing.
Neither compatible rowwise inverse choices nor groupoid hypotheses are needed.
-/
@[expose] public section

noncomputable section
open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SSet.BisimplicialRealization
open CategoryTheory.TheoremA
variable {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y)

/-- The attaching subcomplex inherits every rowwise equivalence. -/
theorem attachmentMap_isRealizationEquivalence
    (h : ∀ n, IsRealizationEquivalence (η.app (op ⦋n⦌))) (n : ℕ) :
    IsRealizationEquivalence (attachmentMap n η) := by
  let : CompactSpace |(Δ[n] : SSet.{u})| := (SimplexCategory.toTopHomeo ⦋n⦌).symm.compactSpace
  let : T2Space |(Δ[n] : SSet.{u})| := (SimplexCategory.toTopHomeo ⦋n⦌).symm.t2Space
  have hmono (Z : SimplicialObject SSet.{u}) :
      Mono ((latching Z n).ι ▷ (∂Δ[n] : SSet.{u})) := by
    rw [NatTrans.mono_iff_mono_app]
    intro q
    apply (mono_iff_injective _).2
    intro x y hxy
    change (x.1.val, x.2) = (y.1.val, y.2) at hxy
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj hxy
    exact Prod.ext (Subtype.ext h₁) h₂
  have := hmono X
  have := hmono Y
  have hl := latchingMap_isRealizationEquivalence η h n
  exact IsRealizationEquivalence.pushout
    (attachment_union_isPushout X n) (attachment_union_isPushout Y n)
    (latchingMap η n ▷ (∂Δ[n] : SSet.{u})) (η.app (op ⦋n⦌) ▷ (∂Δ[n] : SSet.{u}))
    (latchingMap η n ▷ (Δ[n] : SSet.{u})) (attachmentMap n η)
    (by rw [← comp_whiskerRight, ← comp_whiskerRight, latchingMap_ι])
    (by exact whisker_exchange _ _)
    (attachmentMap_boundary n η).symm (attachmentMap_latching n η).symm
    (hl.whiskerRight _) ((h n).whiskerRight _) (hl.whiskerRight _)

/-- The empty outer stage is an initial simplicial set. -/
-- Preserve the public empty-stage initiality witness name for existing downstream references.
def stageZeroIsInitial (X : SimplicialObject SSet.{u}) : IsInitial (stage X 0) :=
  SSet.Subcomplex.isInitialBot.ofIso (SSet.Subcomplex.eqToIso (outerSkeleton_zero X)).symm

/-- Rowwise realization equivalences give equivalences on every finite outer skeleton. -/
theorem stageMap_isRealizationEquivalence
    (h : ∀ n, IsRealizationEquivalence (η.app (op ⦋n⦌))) (n : ℕ) :
    IsRealizationEquivalence (stageMap η n) := by
  induction n with
  | zero =>
      exact IsRealizationEquivalence.of_isInitial _ (stageZeroIsInitial X) (stageZeroIsInitial Y)
  | succ n ih =>
    let : CompactSpace |(Δ[n] : SSet.{u})| := (SimplexCategory.toTopHomeo ⦋n⦌).symm.compactSpace
    let : T2Space |(Δ[n] : SSet.{u})| := (SimplexCategory.toTopHomeo ⦋n⦌).symm.t2Space
    exact IsRealizationEquivalence.pushout
      (attachment_isPushout X n).flip (attachment_isPushout Y n).flip
      (attachmentMap n η) (η.app (op ⦋n⦌) ▷ (Δ[n] : SSet.{u})) (stageMap η n)
      (stageMap η (n + 1))
      (attachmentMap_ι n η).symm (attachmentMap_toStage n η).symm
      (rowToStage_naturality n η).symm (stageInclusion_naturality n η).symm
      (attachmentMap_isRealizationEquivalence η h n) ((h n).whiskerRight _) ih

/-- Every rowwise realization homotopy equivalence induces an equivalence of
the actual diagonal realization, with the given map as its forward map. -/
theorem diagonalMap_isRealizationEquivalence
    (h : ∀ n, IsRealizationEquivalence (η.app (op ⦋n⦌))) :
    IsRealizationEquivalence (diagonalMap η) := by
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
  have hA (n : ℕ) : TopCat.HomotopyExtensionProperty (A.map (homOfLE (Nat.le_succ n))) := by
    have := hmono X n
    exact SSet.homotopyExtensionProperty_realization_mono _
  have hB (n : ℕ) : TopCat.HomotopyExtensionProperty (B.map (homOfLE (Nat.le_succ n))) := by
    have := hmono Y n
    exact SSet.homotopyExtensionProperty_realization_mono _
  choose E hE using stageMap_isRealizationEquivalence η h
  let e := TopCat.sequentialCoconeHomotopyEquiv α hA hB E hE c hc d hd
  have he : e.toFun = (SSet.toTop.map (diagonalMap η)).hom := by
    rw [TopCat.sequentialCoconeHomotopyEquiv_toFun]
    apply congrArg TopCat.Hom.hom
    apply hc.hom_ext
    intro n
    rw [hc.ι_map]
    change SSet.toTop.map (stageMap η n) ≫ SSet.toTop.map (outerSkeleton Y n).ι =
      SSet.toTop.map (outerSkeleton X n).ι ≫ SSet.toTop.map (diagonalMap η)
    simpa only [Functor.map_comp] using congrArg SSet.toTop.map (stageMap_ι η n)
  exact ⟨e, he⟩

/-- A specified rowwise family of actual homotopy equivalences gives an
actual homotopy equivalence on diagonal realizations. -/
def diagonalRealizationHomotopyEquiv
    (e : ∀ n, ContinuousMap.HomotopyEquiv |X.obj (op ⦋n⦌)| |Y.obj (op ⦋n⦌)|)
    (he : ∀ n, (e n).toFun = (SSet.toTop.map (η.app (op ⦋n⦌))).hom) :
    ContinuousMap.HomotopyEquiv |diagonalSSet X| |diagonalSSet Y| := by
  have h := diagonalMap_isRealizationEquivalence η (fun n ↦ ⟨e n, he n⟩)
  let E := h.choose
  have hE := h.choose_spec
  exact {
    toFun := (SSet.toTop.map (diagonalMap η)).hom
    invFun := E.invFun
    left_inv := by rw [← hE]; exact E.left_inv
    right_inv := by rw [← hE]; exact E.right_inv }

@[simp] theorem diagonalRealizationHomotopyEquiv_toFun
    (e : ∀ n, ContinuousMap.HomotopyEquiv |X.obj (op ⦋n⦌)| |Y.obj (op ⦋n⦌)|)
    (he : ∀ n, (e n).toFun = (SSet.toTop.map (η.app (op ⦋n⦌))).hom) :
    (diagonalRealizationHomotopyEquiv η e he).toFun =
      (SSet.toTop.map (diagonalMap η)).hom := rfl

/-- The same rowwise hypothesis gives an equivalence on the existing topological
coend realization. Its forward map is the canonical coend map, identified by
the natural diagonal/iterated-realization isomorphism. -/
def iteratedRealizationHomotopyEquiv
    (e : ∀ n, ContinuousMap.HomotopyEquiv |X.obj (op ⦋n⦌)| |Y.obj (op ⦋n⦌)|)
    (he : ∀ n, (e n).toFun = (SSet.toTop.map (η.app (op ⦋n⦌))).hom) :
    ContinuousMap.HomotopyEquiv (iteratedRealization (X ⋙ SSet.toTop))
      (iteratedRealization (Y ⋙ SSet.toTop)) := by
  refine TopCat.homotopyEquivOfIsoSquare
    (iteratedRealizationMap (Functor.whiskerRight η SSet.toTop))
    (SSet.toTop.map (diagonalMap η))
    (diagonalIteratedRealizationIso X).symm (diagonalIteratedRealizationIso Y).symm
    ?_ (diagonalRealizationHomotopyEquiv η e he) rfl
  apply (cancel_epi (diagonalIteratedRealizationIso X).hom).mp
  simp only [← Category.assoc]
  rw [← diagonalIteratedRealizationIso_naturality]
  simp

@[simp] theorem iteratedRealizationHomotopyEquiv_toFun
    (e : ∀ n, ContinuousMap.HomotopyEquiv |X.obj (op ⦋n⦌)| |Y.obj (op ⦋n⦌)|)
    (he : ∀ n, (e n).toFun = (SSet.toTop.map (η.app (op ⦋n⦌))).hom) :
    (iteratedRealizationHomotopyEquiv η e he).toFun =
      (iteratedRealizationMap (Functor.whiskerRight η SSet.toTop)).hom := rfl

end SSet.BisimplicialRealization

attribute [colib_tag "COL-0242",
  colib_ref "WeibelKBook" "IV, Theorem 3.6.1(i), page 29" "clause"
    "General rowwise homotopy equivalence and the actual diagonal and coend maps"]
  SSet.BisimplicialRealization.diagonalMap_isRealizationEquivalence
  SSet.BisimplicialRealization.diagonalRealizationHomotopyEquiv
  SSet.BisimplicialRealization.iteratedRealizationHomotopyEquiv
