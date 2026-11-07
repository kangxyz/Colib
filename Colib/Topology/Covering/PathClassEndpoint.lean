/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Covering.PathClassEndpointAlgebra
public import Colib.Topology.Homotopy.OpenCover

/-!
# Actual path endpoints in the path-class covering

The endpoint equation is proved locally in genuine bundle charts, then globally
by compact open-cover subdivision. Both arbitrary chart offsets are cancelled.
-/

/-! Implementation source: `Quillen/Topology/Covering/PathClassEndpoint.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual topologies,
path classes, dependent endpoint equalities and covering maps are retained. -/
@[expose] public section
noncomputable section
open Set CategoryTheory Bundle
open scoped unitInterval
universe u
namespace Topology.PathThinNeighborhoods
variable {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
  [LocallyPathConnectedSpace X] (A : PathThinNeighborhoods X) (b : X)

/-- The actual projection with continuity supplied by the constructed covering. -/
abbrev totalProjection :
    letI := (A.prebundle b).totalSpaceTopology
    C(Total b, X) := by
  let := (A.prebundle b).totalSpaceTopology
  exact ⟨Bundle.TotalSpace.proj, (A.isCoveringMap_projection b).continuous⟩

/-- An actual upstairs path lying in one chart has constant discrete coordinate. -/
theorem fiberEquiv_path_eq (c : X) {e₀ e₁ : Total b} :
    letI := (A.prebundle b).totalSpaceTopology
    ∀ (γ : Path e₀ e₁), (∀ t, (γ t).proj ∈ A.neighborhood c) →
      A.fiberEquiv b c e₀.proj e₀.snd = A.fiberEquiv b c e₁.proj e₁.snd := by
  let := (A.prebundle b).totalSpaceTopology
  intro γ hγ
  let T := (A.prebundle b).trivializationOfMemPretrivializationAtlas
    (show A.pretrivialization b c ∈ (A.prebundle b).pretrivializationAtlas from
      Set.mem_range_self c)
  have hT : Continuous (fun t : I => T (γ t)) :=
    continuousOn_univ.mp (T.continuousOn.comp γ.continuous.continuousOn
      (fun t _ => hγ t))
  have hcoord : Continuous (fun t : I =>
      A.fiberEquiv b c (γ t).proj (γ t).snd) := hT.snd
  have hconst := (IsLocallyConstant.iff_continuous _).mpr hcoord
  have h := hconst.apply_eq_of_preconnectedSpace (0 : I) 1
  change (fun e : Total b => A.fiberEquiv b c e.proj e.snd) (γ 0) =
    (fun e : Total b => A.fiberEquiv b c e.proj e.snd) (γ 1) at h
  exact (congrArg (fun e : Total b => A.fiberEquiv b c e.proj e.snd) γ.source).symm.trans
    (h.trans (congrArg (fun e : Total b => A.fiberEquiv b c e.proj e.snd) γ.target))

/-- The exact endpoint equation in one actual chart. -/
theorem path_class_endpoint_local (c : X) {e₀ e₁ : Total b} :
    letI := (A.prebundle b).totalSpaceTopology
    ∀ (γ : Path e₀ e₁), (∀ t, (γ t).proj ∈ A.neighborhood c) →
      e₀.snd.toQuotient.trans (.mk (γ.map (A.totalProjection b).continuous)) =
        e₁.snd.toQuotient := by
  let := (A.prebundle b).totalSpaceTopology
  intro γ hγ
  have h₀ : e₀.proj ∈ A.neighborhood c := by simpa only [γ.source] using hγ 0
  have h₁ : e₁.proj ∈ A.neighborhood c := by simpa only [γ.target] using hγ 1
  exact congrArg PathClassFiber.toQuotient
    (A.endpointAction_eq_of_fiberEquiv_eq b c h₀ h₁
      (γ.map (A.totalProjection b).continuous) hγ e₀.snd e₁.snd
      (A.fiberEquiv_path_eq b c γ hγ))

private theorem projectionClass_symm {e₀ e₁ : Total b} :
    letI := (A.prebundle b).totalSpaceTopology
    ∀ (q : Path.Homotopic.Quotient e₀ e₁),
      q.symm.map (A.totalProjection b) = (q.map (A.totalProjection b)).symm := by
  let := (A.prebundle b).totalSpaceTopology
  intro q
  exact Quotient.inductionOn q (fun _ => rfl)

private theorem projectionClass_trans {e₀ e₁ e₂ : Total b} :
    letI := (A.prebundle b).totalSpaceTopology
    ∀ (q : Path.Homotopic.Quotient e₀ e₁) (r : Path.Homotopic.Quotient e₁ e₂),
      (q.trans r).map (A.totalProjection b) =
        (q.map (A.totalProjection b)).trans (r.map (A.totalProjection b)) := by
  let := (A.prebundle b).totalSpaceTopology
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro q r
  exact congrArg Path.Homotopic.Quotient.mk (q.map_trans r (A.totalProjection b).continuous)

/-- The endpoint equation defines a subgroupoid of the actual total space. -/
def endpointSubgroupoid :
    letI := (A.prebundle b).totalSpaceTopology
    Subgroupoid (FundamentalGroupoid (Total b)) := by
  let := (A.prebundle b).totalSpaceTopology
  exact {
    arrows e₀ e₁ := {q | e₀.as.snd.toQuotient.trans
      (q.map (A.totalProjection b)) = e₁.as.snd.toQuotient}
    inv := by
      intro e₀ e₁ q hq
      change e₁.as.snd.toQuotient.trans
        (q.symm.map (A.totalProjection b)) = e₀.as.snd.toQuotient
      rw [A.projectionClass_symm b, ← hq]
      simp
    mul := by
      intro e₀ e₁ e₂ q hq r hr
      change e₀.as.snd.toQuotient.trans
        ((q.trans r).map (A.totalProjection b)) = e₂.as.snd.toQuotient
      rw [A.projectionClass_trans b, ← Path.Homotopic.Quotient.trans_assoc, hq, hr] }

/-- The endpoint formula for every original continuous path in the constructed
covering total space, using the actual open cover rather than a PL premise. -/
theorem path_class_endpoint {e₀ e₁ : Total b} :
    letI := (A.prebundle b).totalSpaceTopology
    ∀ (γ : Path e₀ e₁),
      e₀.snd.toQuotient.trans (.mk (γ.map (A.totalProjection b).continuous)) =
        e₁.snd.toQuotient := by
  let := (A.prebundle b).totalSpaceTopology
  intro γ
  refine FundamentalGroupoid.path_mem_of_openCover
    (A.endpointSubgroupoid b)
    (fun c => (A.pretrivialization b c).source)
    (fun c => (A.prebundle b).isOpen_source (A.pretrivialization b c))
    (fun e _ => Set.mem_iUnion.mpr ⟨e.proj, A.mem_neighborhood e.proj⟩)
    ?_ γ
  intro c e₀ e₁ p hp
  change e₀.snd.toQuotient.trans (.mk (p.map (A.totalProjection b).continuous)) =
    e₁.snd.toQuotient
  exact A.path_class_endpoint_local b c p (fun t => hp (Set.mem_range_self t))

/-- The equivalent exact action statement in the named discrete fiber. -/
theorem endpointAction_path {e₀ e₁ : Total b} :
    letI := (A.prebundle b).totalSpaceTopology
    ∀ (γ : Path e₀ e₁),
      endpointAction b e₀.snd (.mk (γ.map (A.totalProjection b).continuous)) = e₁.snd := by
  let := (A.prebundle b).totalSpaceTopology
  intro γ
  apply PathClassFiber.ext
  exact A.path_class_endpoint b γ

/-- Endpoint control also holds for arbitrary actual homotopy classes upstairs. -/
theorem quotient_class_endpoint {e₀ e₁ : Total b} :
    letI := (A.prebundle b).totalSpaceTopology
    ∀ (q : Path.Homotopic.Quotient e₀ e₁),
      e₀.snd.toQuotient.trans (q.map (A.totalProjection b)) = e₁.snd.toQuotient := by
  let := (A.prebundle b).totalSpaceTopology
  intro q
  exact Quotient.inductionOn q (fun q => A.path_class_endpoint b q)

end Topology.PathThinNeighborhoods
