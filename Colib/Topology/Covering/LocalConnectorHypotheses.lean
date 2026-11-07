/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Covering.PathClassPrebundle
public import Colib.Topology.LocalEquiconnection
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.Topology.Compactness.Compact

/-!
# Actual local-connector hypotheses for the path-class covering

The original topology and actual continuous connector are used throughout.
A tube argument proves local path connectedness;
a homotopy of the slice inclusion proves ambient path thinness. No covering
or homotopy-type invariance of local topology is assumed.
-/

/-! Implementation source: `Quillen/Topology/Covering/LocalConnectorHypotheses.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual topologies,
path classes, dependent endpoint equalities and covering maps are retained. -/
@[expose] public section
noncomputable section
open Set Topology
open scoped unitInterval
universe u
namespace Topology
variable {X : Type u} [TopologicalSpace X]

/-- Ambient path thinness is inherited by smaller subsets. -/
theorem AmbientPathThin.mono {U V : Set X} (hU : AmbientPathThin U) (hVU : V ⊆ U) :
    AmbientPathThin V := fun _ _ p q hp hq =>
  hU p q (fun t => hVU (hp t)) (fun t => hVU (hq t))

/-- Even an unbased homotopy from a constant map to the actual inclusion makes
all path classes with fixed endpoints in the subset equal in the ambient space.
The endpoint tracks are retained and cancelled in the genuine path quotient. -/
theorem ambientPathThin_of_constant_homotopy {U : Set X} (a : X)
    (H : (ContinuousMap.const U a).Homotopy
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))) : AmbientPathThin U := by
  intro x y p q hp hq
  let x' : U := ⟨x, by simpa using hp 0⟩
  let y' : U := ⟨y, by simpa using hp 1⟩
  let p' : Path x' y' :=
    { toFun t := ⟨p t, hp t⟩
      continuous_toFun := p.continuous.subtype_mk _
      source' := Subtype.ext p.source
      target' := Subtype.ext p.target }
  let q' : Path x' y' :=
    { toFun t := ⟨q t, hq t⟩
      continuous_toFun := q.continuous.subtype_mk _
      source' := Subtype.ext q.source
      target' := Subtype.ext q.target }
  have hpmap : p'.map continuous_subtype_val = p := by ext t; rfl
  have hqmap : q'.map continuous_subtype_val = q := by ext t; rfl
  have hpconst : p'.map (ContinuousMap.const U a).continuous = Path.refl a := by ext t; rfl
  have hqconst : q'.map (ContinuousMap.const U a).continuous = Path.refl a := by ext t; rfl
  have hpH := Path.Homotopic.Quotient.eq.mpr (Path.Homotopic.map_trans_evalAt H p')
  have hqH := Path.Homotopic.Quotient.eq.mpr (Path.Homotopic.map_trans_evalAt H q')
  simp only [hpmap, hpconst, Path.Homotopic.Quotient.mk_trans] at hpH
  simp only [hqmap, hqconst, Path.Homotopic.Quotient.mk_trans] at hqH
  apply Path.Homotopic.Quotient.eq.mp
  have heq := hpH.symm.trans hqH
  have hc := congrArg (fun r => (Path.Homotopic.Quotient.mk (H.evalAt x')).symm.trans r) heq
  simpa only [← Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans] using hc

namespace LocalEquiconnection
variable (E : LocalEquiconnection X)

/-- The original open slice of the connector domain at the first endpoint. -/
def slice (x : X) : Set X := {y | (x, y) ∈ E.domain}

theorem isOpen_slice (x : X) : IsOpen (E.slice x) :=
  E.isOpen_domain.preimage (continuous_const.prodMk continuous_id)

theorem mem_slice (x : X) : x ∈ E.slice x := E.diagonal_mem x

/-- The actual connector restricted to this slice, retaining joint continuity. -/
def sliceConnector (x : X) : C(E.slice x × I, X) where
  toFun p := E.connector (⟨(x, p.1.1), p.1.2⟩, p.2)
  continuous_toFun := E.connector.continuous.comp
    ((continuous_const.prodMk (continuous_subtype_val.comp continuous_fst)).subtype_mk _
      |>.prodMk continuous_snd)

/-- A genuine homotopy from the constant map to the inclusion of the slice. -/
def sliceHomotopy (x : X) :
    (ContinuousMap.const (E.slice x) x).Homotopy
      (⟨Subtype.val, continuous_subtype_val⟩ : C(E.slice x, X)) where
  toFun p := E.sliceConnector x (p.2, p.1)
  continuous_toFun := (E.sliceConnector x).continuous.comp (continuous_snd.prodMk continuous_fst)
  map_zero_left y := E.connector_zero ⟨(x, y.1), y.2⟩
  map_one_left y := E.connector_one ⟨(x, y.1), y.2⟩

/-- This slice has trivial ambient path classes for every pair of endpoints. -/
theorem ambientPathThin_slice (x : X) : AmbientPathThin (E.slice x) :=
  ambientPathThin_of_constant_homotopy x (E.sliceHomotopy x)

include E in
/-- Compact interval control near the fixed whole diagonal yields an actual
neighborhood inside each open-set pathcomponent. -/
theorem pathComponentIn_mem_nhds {O : Set X} (hO : IsOpen O) {x : X} (hx : x ∈ O) :
    pathComponentIn O x ∈ 𝓝 x := by
  let x' : E.slice x := ⟨x, E.mem_slice x⟩
  let N : Set (E.slice x × I) := (E.sliceConnector x) ⁻¹' O
  have hN : IsOpen N := hO.preimage (E.sliceConnector x).continuous
  have hcompact : IsCompact (univ : Set I) := isCompact_univ
  have hsubset : ({x'} : Set (E.slice x)) ×ˢ (univ : Set I) ⊆ N := by
    rintro ⟨y, t⟩ ⟨hy, _⟩
    have hy' : y = x' := hy
    subst y
    change E.connector (⟨(x, x), E.mem_slice x⟩, t) ∈ O
    simpa only [E.connector_diagonal] using hx
  obtain ⟨V, T, hV, _hT, hxV, hIT, hVT⟩ :=
    generalized_tube_lemma isCompact_singleton hcompact hN hsubset
  refine mem_nhds_iff.mpr ⟨Subtype.val '' V, ?_,
    (E.isOpen_slice x).isOpenMap_subtype_val V hV, ?_⟩
  · rintro y ⟨z, hz, rfl⟩
    refine ⟨(E.sliceHomotopy x).evalAt z, ?_⟩
    intro t
    exact hVT ⟨hz, hIT (mem_univ t)⟩
  · exact ⟨x', hxV (mem_singleton x'), rfl⟩

include E in
/-- The actual local connector proves local path connectedness of the original
space, via open pathcomponents rather than assumed convex neighborhoods. -/
theorem locallyPathConnectedSpace : LocallyPathConnectedSpace X :=
  locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds.mpr
    (fun _ _ hO hx => E.pathComponentIn_mem_nhds hO hx)

/-- Open pathcomponents of connector slices supply precisely the local geometric
input needed by `PathThinNeighborhoods.prebundle`. -/
def pathThinNeighborhoods : PathThinNeighborhoods X := by
  letI := E.locallyPathConnectedSpace
  exact
    { neighborhood x := pathComponentIn (E.slice x) x
      isOpen_neighborhood x := (E.isOpen_slice x).pathComponentIn x
      mem_neighborhood x := mem_pathComponentIn_self (E.mem_slice x)
      isPathConnected_neighborhood x := isPathConnected_pathComponentIn (E.mem_slice x)
      ambientPathThin x := (E.ambientPathThin_slice x).mono pathComponentIn_subset }

end LocalEquiconnection
end Topology
