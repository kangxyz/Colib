/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.FundamentalGroup
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransportGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-! # The original path transport is fundamental-group conjugation -/
/-! Implementation source: `Quillen/Topology/HomotopyGroups/PathTransportFundamentalGroup.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual maps, endpoint paths,
universes and signs are retained, with native Colib dependencies. -/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped unitInterval
universe u v
namespace Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {X : Type u} [TopologicalSpace X]

/-- Evaluation follows each original free path through its own parameter. -/
def freePathEvaluationHomotopy : (freePathEvaluation X 0).Homotopy (freePathEvaluation X 1) where
  toFun p := p.2 p.1
  continuous_toFun := continuous_snd.eval continuous_fst
  map_zero_left _ := rfl
  map_one_left _ := rfl

theorem fundamentalGroup_map_eval_transport {x y : X} (γ : Path x y)
    (a : FundamentalGroup C(unitInterval, X) γ.toContinuousMap) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath γ
      (FundamentalGroup.mapOfEq (freePathEvaluation X 0) γ.source a) =
        FundamentalGroup.mapOfEq (freePathEvaluation X 1) γ.target a := by
  rcases γ with ⟨p, h₀, h₁⟩
  cases h₀
  cases h₁
  let H := freePathEvaluationHomotopy (X := X)
  have h := (FundamentalGroupoidFunctor.homotopicMapsNatIso H).naturality a
  simp only [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl]
  change Groupoid.inv (⟦(⟨p, rfl, rfl⟩ : Path (p 0) (p 1))⟧ : Path.Homotopic.Quotient _ _) ≫
    (FundamentalGroupoid.map (freePathEvaluation X 0)).map a ≫
      (⟦(⟨p, rfl, rfl⟩ : Path (p 0) (p 1))⟧ : Path.Homotopic.Quotient _ _) =
    (FundamentalGroupoid.map (freePathEvaluation X 1)).map a
  change (FundamentalGroupoid.map (freePathEvaluation X 0)).map a ≫
      (⟦(⟨p, rfl, rfl⟩ : Path (p 0) (p 1))⟧ : Path.Homotopic.Quotient _ _) =
    (⟦(⟨p, rfl, rfl⟩ : Path (p 0) (p 1))⟧ : Path.Homotopic.Quotient _ _) ≫
      (FundamentalGroupoid.map (freePathEvaluation X 1)).map a at h
  rw [h]
  simp

/-- The original evaluation-based transport is exactly conjugation by the original path class. -/
theorem piOneEquivFundamentalGroup_pathTransport {x y : X} (γ : Path x y)
    (a : HomotopyGroup.Pi 1 X x) :
    HomotopyGroup.pi1MulEquivFundamentalGroup (pathTransport γ 1 a) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath γ
        (HomotopyGroup.pi1MulEquivFundamentalGroup a) := by
  obtain ⟨b, rfl⟩ := (pathStartEquiv γ 1).surjective a
  rw [pathStartEquiv_apply, pathTransport_homotopyGroupMap_start]
  rw [HomotopyGroup.pi1MulEquivFundamentalGroup_naturality,
    HomotopyGroup.pi1MulEquivFundamentalGroup_naturality]
  exact (fundamentalGroup_map_eval_transport γ _).symm

variable {Y : Type v} [TopologicalSpace Y]
/-- Endpoint paths give the same corrected fundamental-group map into an abelian target. -/
theorem fundamentalGroup_homotopy_corrected {f g : C(X, Y)} {x : X} {y : Y}
    (H : f.Homotopy g) (γ : Path (f x) y) (δ : Path (g x) y)
    (hc : ∀ a b : FundamentalGroup Y y, a * b = b * a)
    (a : FundamentalGroup X x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath γ (FundamentalGroup.map f x a) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath δ (FundamentalGroup.map g x a) := by
  let cγ : FundamentalGroupoid.mk (f x) ⟶ FundamentalGroupoid.mk y := ⟦γ⟧
  let cδ : FundamentalGroupoid.mk (g x) ⟶ FundamentalGroupoid.mk y := ⟦δ⟧
  let t : FundamentalGroupoid.mk (f x) ⟶ FundamentalGroupoid.mk (g x) := ⟦H.evalAt x⟧
  let u : FundamentalGroup Y y := inv cγ ≫ (FundamentalGroupoid.map f).map a ≫ cγ
  let v : FundamentalGroup Y y := inv cδ ≫ (FundamentalGroupoid.map g).map a ≫ cδ
  let k : FundamentalGroup Y y := inv cγ ≫ t ≫ cδ
  have hn : (FundamentalGroupoid.map f).map a ≫ t =
      t ≫ (FundamentalGroupoid.map g).map a :=
    (FundamentalGroupoidFunctor.homotopicMapsNatIso H).naturality a
  have huv : u ≫ k = k ≫ v := by
    dsimp [u, v, k]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    simpa only [Category.assoc, FundamentalGroupoid.map_map] using
      congrArg (fun b => inv cγ ≫ b ≫ cδ) hn
  have he : u = v := (cancel_mono k).1 (huv.trans (hc v k))
  simpa [u, v, cγ, cδ, FundamentalGroup.fundamentalGroupMulEquivOfPath,
    Groupoid.isoEquivHom, Iso.conj_apply, FundamentalGroup.map_apply,
    FundamentalGroupoid.map_map] using he

/-- Homotopic maps into an abelian fundamental group retain the same map with any endpoint paths. -/
theorem piOne_homotopy_corrected {f g : C(X, Y)} {x : X} {y : Y}
    (H : f.Homotopy g) (γ : Path (f x) y) (δ : Path (g x) y)
    (hc : ∀ a b : HomotopyGroup.Pi 1 Y y, a * b = b * a) :
    (pathTransportMulEquiv γ 0).toMonoidHom.comp (HomotopyGroup.piMap 0 f rfl) =
      (pathTransportMulEquiv δ 0).toMonoidHom.comp (HomotopyGroup.piMap 0 g rfl) := by
  have hcf : ∀ a b : FundamentalGroup Y y, a * b = b * a := by
    intro a b
    let e := HomotopyGroup.pi1MulEquivFundamentalGroup (X := Y) (x := y)
    apply e.symm.injective
    simp only [map_mul]
    exact hc (e.symm a) (e.symm b)
  ext a
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  change HomotopyGroup.pi1MulEquivFundamentalGroup
      (pathTransport γ 1 (HomotopyGroup.map f rfl a)) =
    HomotopyGroup.pi1MulEquivFundamentalGroup (pathTransport δ 1 (HomotopyGroup.map g rfl a))
  rw [piOneEquivFundamentalGroup_pathTransport, piOneEquivFundamentalGroup_pathTransport,
    HomotopyGroup.pi1MulEquivFundamentalGroup_naturality,
    HomotopyGroup.pi1MulEquivFundamentalGroup_naturality]
  simpa only [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl,
    FundamentalGroup.map_apply] using
    fundamentalGroup_homotopy_corrected H γ δ hcf
      (HomotopyGroup.pi1MulEquivFundamentalGroup a)

end Topology
