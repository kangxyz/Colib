/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Covering.PathClassEndpoint
public import Colib.Topology.Covering.LocalConnectorHypotheses
public import Mathlib.Topology.Homotopy.Lifting

/-!
# Simple connectedness of the constructed path-class total space

Actual covering path lifts reach every literal based path
class by the endpoint equation. Covering injectivity and the same equation
then force uniqueness of all upstairs path classes. Neither conclusion is an
input to this construction.
-/

/-! Implementation source: `Quillen/Topology/Covering/PathClassSimplyConnected.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual topologies,
path classes, dependent endpoint equalities and covering maps are retained. -/
@[expose] public section
noncomputable section
open Set Bundle
open scoped unitInterval
universe u
namespace Topology.PathThinNeighborhoods
variable {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
  [LocallyPathConnectedSpace X] (A : PathThinNeighborhoods X) (b : X)

local notation "CoverPath" => @Path (Total b) (FiberPrebundle.totalSpaceTopology (prebundle A b))
local notation "CoverClass" =>
  @Path.Homotopic.Quotient (Total b) (FiberPrebundle.totalSpaceTopology (prebundle A b))

/-- The literal neutral based-path-class point, without chart normalization. -/
def totalBasepoint : Total b := ⟨b, PathClassFiber.ofQuotient (.refl b)⟩

/-- The actual covering lift of a path starting at a specified literal fiber element. -/
def pathLift {x y : X} (r : PathClassFiber b x) (p : Path x y) :
    @ContinuousMap I (Total b) _ (A.prebundle b).totalSpaceTopology := by
  let := (A.prebundle b).totalSpaceTopology
  exact (A.isCoveringMap_projection b).liftPath p ⟨x, r⟩ p.source

/-- The lift starts at the specified actual total-space point. -/
theorem pathLift_zero {x y : X} (r : PathClassFiber b x) (p : Path x y) :
    A.pathLift b r p 0 = ⟨x, r⟩ := by
  let := (A.prebundle b).totalSpaceTopology
  exact (A.isCoveringMap_projection b).liftPath_zero p ⟨x, r⟩ p.source

/-- At every time the lifted path projects to the original path. -/
theorem pathLift_proj {x y : X} (r : PathClassFiber b x) (p : Path x y) (t : I) :
    (A.pathLift b r p t).proj = p t := by
  let := (A.prebundle b).totalSpaceTopology
  exact congr_fun ((A.isCoveringMap_projection b).liftPath_lifts p ⟨x, r⟩ p.source) t

omit [PathConnectedSpace X] [LocallyPathConnectedSpace X] in
private theorem class_trans_cast_right {a x y z : X}
    (r : Path.Homotopic.Quotient a x) (q : Path.Homotopic.Quotient x y) (h : z = y) :
    r.trans (q.cast rfl h) = (r.trans q).cast rfl h := by
  cases h
  simp only [Path.Homotopic.Quotient.cast_rfl_rfl]

omit [PathConnectedSpace X] [LocallyPathConnectedSpace X] in
private theorem total_mk_class_cast {x y : X} (h : x = y)
    (q : Path.Homotopic.Quotient b y) :
    (⟨x, PathClassFiber.ofQuotient (q.cast rfl h)⟩ : Total b) =
      ⟨y, PathClassFiber.ofQuotient q⟩ := by
  cases h
  simp only [Path.Homotopic.Quotient.cast_rfl_rfl]

/-- The exact endpoint class, with the necessary dependent endpoint cast displayed. -/
theorem pathLift_endpoint_class {x y : X} (r : PathClassFiber b x) (p : Path x y) :
    (A.pathLift b r p 1).snd.toQuotient =
      (r.toQuotient.trans (.mk p)).cast rfl
        ((A.pathLift_proj b r p 1).trans p.target) := by
  let := (A.prebundle b).totalSpaceTopology
  let γ : CoverPath (⟨x, r⟩ : Total b) (A.pathLift b r p 1) :=
    ⟨A.pathLift b r p, A.pathLift_zero b r p, rfl⟩
  have hproj := (A.pathLift_proj b r p 1).trans p.target
  have hmap : γ.map (A.totalProjection b).continuous = p.cast rfl hproj := by
    ext t
    exact A.pathLift_proj b r p t
  have h := A.path_class_endpoint b γ
  rw [hmap, Path.Homotopic.Quotient.mk_cast, class_trans_cast_right] at h
  exact h.symm

/-- The literal lifted endpoint is the chronologically composed based class.
Its proof retains, then eliminates, the displayed dependent endpoint cast. -/
theorem pathLift_endpoint {x y : X} (r : PathClassFiber b x) (p : Path x y) :
    A.pathLift b r p 1 = ⟨y, endpointAction b r (.mk p)⟩ := by
  let := (A.prebundle b).totalSpaceTopology
  let hproj := (A.pathLift_proj b r p 1).trans p.target
  calc
    A.pathLift b r p 1 =
        ⟨(A.pathLift b r p 1).proj,
          PathClassFiber.ofQuotient ((r.toQuotient.trans (.mk p)).cast rfl hproj)⟩ := by
      apply congrArg (Bundle.TotalSpace.mk (A.pathLift b r p 1).proj)
      apply PathClassFiber.ext
      exact A.pathLift_endpoint_class b r p
    _ = ⟨y, endpointAction b r (.mk p)⟩ :=
      total_mk_class_cast b hproj (r.toQuotient.trans (.mk p))

/-- The actual lift, packaged as a path to its proven literal endpoint. -/
def pathToEndpoint {x y : X} (r : PathClassFiber b x) (p : Path x y) :
    CoverPath (⟨x, r⟩ : Total b) ⟨y, endpointAction b r (.mk p)⟩ := by
  let := (A.prebundle b).totalSpaceTopology
  exact ⟨A.pathLift b r p, A.pathLift_zero b r p, A.pathLift_endpoint b r p⟩

/-- Every literal based class can be reached from the neutral total point. -/
theorem joined_totalBasepoint (e : Total b) :
    @Joined (Total b) (A.prebundle b).totalSpaceTopology (totalBasepoint b) e := by
  let := (A.prebundle b).totalSpaceTopology
  rcases e with ⟨x, r⟩
  change Joined (totalBasepoint b) ⟨x, PathClassFiber.ofQuotient r.toQuotient⟩
  refine Quotient.inductionOn r.toQuotient ?_
  intro p
  have hp := A.pathToEndpoint b (PathClassFiber.ofQuotient (.refl b)) p
  have he : endpointAction b (PathClassFiber.ofQuotient (.refl b)) (.mk p) =
      PathClassFiber.ofQuotient (.mk p) := by
    apply PathClassFiber.ext
    change (Path.Homotopic.Quotient.refl b).trans (.mk p) = .mk p
    exact Path.Homotopic.Quotient.refl_trans (.mk p)
  exact ⟨hp.cast rfl (congrArg (Bundle.TotalSpace.mk x) he).symm⟩

/-- Actual path connectedness of the chart-generated total space. -/
theorem total_pathConnectedSpace :
    @PathConnectedSpace (Total b) (A.prebundle b).totalSpaceTopology := by
  let := (A.prebundle b).totalSpaceTopology
  exact {
    nonempty := ⟨totalBasepoint b⟩
    joined e₀ e₁ := (A.joined_totalBasepoint b e₀).symm.trans (A.joined_totalBasepoint b e₁) }

/-- Any two upstairs classes have equal projected classes, by cancellation of
one actual initial based class in the endpoint equation. -/
theorem projected_class_eq {e₀ e₁ : Total b} :
    letI := (A.prebundle b).totalSpaceTopology
    ∀ (p q : Path.Homotopic.Quotient e₀ e₁),
      p.map (A.totalProjection b) = q.map (A.totalProjection b) := by
  let := (A.prebundle b).totalSpaceTopology
  intro p q
  have h := (A.quotient_class_endpoint b p).trans (A.quotient_class_endpoint b q).symm
  have hc := congrArg (fun r => e₀.snd.toQuotient.symm.trans r) h
  simpa only [← Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans] using hc

/-- Covering injectivity turns exact projected-class equality into upstairs uniqueness. -/
theorem total_pathClass_subsingleton (e₀ e₁ : Total b) :
    Subsingleton (CoverClass e₀ e₁) := by
  let := (A.prebundle b).totalSpaceTopology
  refine ⟨fun p q => ?_⟩
  apply (A.isCoveringMap_projection b).injective_path_homotopic_map e₀ e₁
  exact A.projected_class_eq b p q

/-- The constructed path-class covering total space is genuinely simply connected. -/
theorem total_simplyConnectedSpace :
    @SimplyConnectedSpace (Total b) (A.prebundle b).totalSpaceTopology := by
  let := (A.prebundle b).totalSpaceTopology
  exact simply_connected_iff_paths_homotopic.mpr
    ⟨A.total_pathConnectedSpace b, A.total_pathClass_subsingleton b⟩

end Topology.PathThinNeighborhoods

namespace Topology.LocalEquiconnection
variable {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]

/-- An actual local connector yields a surjective covering with simply connected
literal path-class total space. No supplied universal cover is an input. -/
theorem exists_simplyConnected_pathClass_cover (E : LocalEquiconnection X) (b : X) :
    letI := E.locallyPathConnectedSpace
    let A := E.pathThinNeighborhoods
    letI := (A.prebundle b).totalSpaceTopology
    IsCoveringMap (Bundle.TotalSpace.proj : PathThinNeighborhoods.Total b → X) ∧
      Function.Surjective (Bundle.TotalSpace.proj : PathThinNeighborhoods.Total b → X) ∧
      SimplyConnectedSpace (PathThinNeighborhoods.Total b) := by
  let := E.locallyPathConnectedSpace
  let A := E.pathThinNeighborhoods
  exact ⟨A.isCoveringMap_projection b,
    PathThinNeighborhoods.projection_surjective b, A.total_simplyConnectedSpace b⟩

end Topology.LocalEquiconnection
