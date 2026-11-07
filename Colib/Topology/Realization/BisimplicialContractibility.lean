/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.TwoSidedBar.ZeroFiber
public import Colib.Topology.Realization.BisimplicialEquivalence
public import Colib.Topology.Homotopy.ContractibleMap
public import Colib.Topology.Realization.Connectivity

/-!
# Connectivity and contractibility of genuine bisimplicial realizations

Every diagonal vertex comes from the original zero row, so path-connectedness of that row
implies path-connectedness of the diagonal. Actual contractible rows imply contractibility
of the original diagonal using the established realization-equivalence theorem. The auxiliary
map equivalence retains the specified continuous map between arbitrary contractible spaces.
-/
/-! Implementation provenance: `Quillen/Topology/Realization/BisimplicialContractibility.lean`
at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, hypotheses,
path coordinates and universe parameters are retained. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
namespace SSet

/-- All vertices of a bisimplicial diagonal lie in its original zero row. -/
theorem diagonal_pathConnected_of_zero_row (H : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    [PathConnectedSpace |H.obj (op ⦋0⦌)|] : PathConnectedSpace |diagonalSSet H| where
  nonempty := ⟨SSet.toTop.map (TwoSidedBar.zeroDiagonalInclusion H)
    (Classical.arbitrary |H.obj (op ⦋0⦌)|)⟩
  joined x y := by
    obtain ⟨a, ha⟩ := realization_joined_vertex x
    obtain ⟨b, hb⟩ := realization_joined_vertex y
    have h := (PathConnectedSpace.joined (realizationPoint (X := H.obj (op ⦋0⦌)) a)
      (realizationPoint (X := H.obj (op ⦋0⦌)) b)).map
        (SSet.toTop.map (TwoSidedBar.zeroDiagonalInclusion H)).hom.continuous
    rw [TwoSidedBar.zeroDiagonalInclusion_realizationPoint,
      TwoSidedBar.zeroDiagonalInclusion_realizationPoint] at h
    exact ha.symm.trans (h.trans hb)

/-- Original rowwise contractions give contractibility of the original diagonal realization. -/
theorem diagonal_contractible_of_rows (H : SimplexCategoryᵒᵖ ⥤ SSet.{u})
    (h : ∀ n : SimplexCategory, ContractibleSpace |H.obj (op n)|) :
    ContractibleSpace |diagonalSSet H| := by
  let D : SSet.{u} := Δ[0]
  let v : D.obj (op ⦋0⦌) := SSet.stdSimplex.const 0 0 _
  let η : H ⟶ (Functor.const _).obj D := {
    app n := SSet.const v
    naturality n m α := by ext k z : 4; rfl }
  let : ContractibleSpace |D| := by
    let : ContractibleSpace |nerve (ULift.{u} (Fin 1))| := by
      change ContractibleSpace (ClassifyingSpace (ULift.{u} (Fin 1)))
      infer_instance
    exact (TopCat.homeoOfIso (SSet.toTop.mapIso (SSet.stdSimplex.isoNerve 0))).contractibleSpace
  let : ContractibleSpace |diagonalSSet ((Functor.const _).obj D)| :=
    (TopCat.homeoOfIso (SSet.toTop.mapIso (TheoremA.diagonalConstantIso D))).contractibleSpace
  apply (BisimplicialRealization.diagonalRealizationHomotopyEquiv η
    (fun n ↦ @ContinuousMap.homotopyEquivOfContractible |H.obj (op ⦋n⦌)| |D| _ _ (h ⦋n⦌) _
      (SSet.toTop.map (η.app (op ⦋n⦌))).hom (Classical.arbitrary _)) (fun _ ↦
        rfl)).contractibleSpace

end SSet
