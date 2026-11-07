/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# The based-path-class prebundle over an ambient-thin open cover

An actual covering projection is constructed on the literal dependent
based-path-class total space. Simple connectedness of that total space is
a separate gate and is not an input or conclusion of this producer.

Local paths are arbitrary choices. Their continuity is never assumed; the
transition functions are proved locally constant using ambient path thinness
and the original base's local path connectedness. All class compositions use
`Path.Homotopic.Quotient.trans`, avoiding the opposite group-product convention.
-/

/-! Implementation source: `Quillen/Topology/Covering/PathClassPrebundle.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual topologies,
path classes, dependent endpoint equalities and covering maps are retained. -/
@[expose] public section
noncomputable section
open Set Function Topology Bundle
open scoped unitInterval
universe u
namespace Topology

variable {X : Type u} [TopologicalSpace X]

/-- Paths contained in this set have a unique ambient class for their endpoints.
The homotopy is in `X`; it need not remain in the displayed set. -/
def AmbientPathThin (U : Set X) : Prop :=
  ∀ ⦃x y : X⦄ (p q : Path x y),
    (∀ t, p t ∈ U) → (∀ t, q t ∈ U) → p.Homotopic q

/-- Explicit local geometric data, containing neither a covering nor a desired
conclusion about homotopy groups of a total space. -/
structure PathThinNeighborhoods (X : Type u) [TopologicalSpace X] where
  /-- The displayed open pathconnected ambient-thin neighborhood at each base point. -/
  neighborhood : X → Set X
  isOpen_neighborhood : ∀ x, IsOpen (neighborhood x)
  mem_neighborhood : ∀ x, x ∈ neighborhood x
  isPathConnected_neighborhood : ∀ x, IsPathConnected (neighborhood x)
  ambientPathThin : ∀ x, AmbientPathThin (neighborhood x)

/-- A named copy of the genuine path quotient, so its discrete fibre topology
does not install a topology on Mathlib's untagged fundamental groups. -/
def PathClassFiber (b x : X) := Path.Homotopic.Quotient b x

instance (b x : X) : TopologicalSpace (PathClassFiber b x) := ⊥
instance (b x : X) : DiscreteTopology (PathClassFiber b x) := ⟨rfl⟩

namespace PathClassFiber
/-- Read the actual path class without unfolding the fibre's topology tag. -/
def toQuotient {b x : X} (r : PathClassFiber b x) : Path.Homotopic.Quotient b x := r
/-- Place an actual path class in the discrete fibre copy. -/
def ofQuotient {b x : X} (r : Path.Homotopic.Quotient b x) : PathClassFiber b x := r
@[simp] theorem toQuotient_ofQuotient {b x : X} (r : Path.Homotopic.Quotient b x) :
    (ofQuotient r).toQuotient = r := rfl
@[simp] theorem ofQuotient_toQuotient {b x : X} (r : PathClassFiber b x) :
    ofQuotient r.toQuotient = r := rfl
@[ext] theorem ext {b x : X} {r s : PathClassFiber b x}
    (h : r.toQuotient = s.toQuotient) : r = s := h
end PathClassFiber

/-- The common discrete model is the genuine fundamental group as a type. -/
def pathClassModelEquivFundamentalGroup (b : X) :
    PathClassFiber b b ≃ FundamentalGroup X b :=
  (CategoryTheory.End.homEquiv (X := FundamentalGroupoid.mk b)).symm

namespace PathThinNeighborhoods
variable (A : PathThinNeighborhoods X) [PathConnectedSpace X] (b : X)

/-- A local path selected solely from actual path connectedness. -/
def localPath (c y : X) (hy : y ∈ A.neighborhood c) : Path c y :=
  (A.isPathConnected_neighborhood c |>.joinedIn c (A.mem_neighborhood c) y hy).somePath

omit [PathConnectedSpace X] in
theorem localPath_mem (c y : X) (hy : y ∈ A.neighborhood c) (t : I) :
    A.localPath c y hy t ∈ A.neighborhood c :=
  (A.isPathConnected_neighborhood c |>.joinedIn c (A.mem_neighborhood c) y hy).somePath_mem t

/-- The chosen based path class on one chart, extended arbitrarily off its open
set only to make the pretrivialization functions total. -/
def chartClass (c y : X) : Path.Homotopic.Quotient b y := by
  classical
  exact if hy : y ∈ A.neighborhood c then
    .mk ((PathConnectedSpace.somePath b c).trans (A.localPath c y hy))
  else .mk (PathConnectedSpace.somePath b y)

omit [PathConnectedSpace X] in
private theorem trans_mem {U : Set X} {x y z : X} (p : Path x y) (q : Path y z)
    (hp : ∀ t, p t ∈ U) (hq : ∀ t, q t ∈ U) (t : I) :
    p.trans q t ∈ U := by
  rw [Path.trans_apply]
  split <;> [exact hp _; exact hq _]

/-- Moving inside the chart transports the arbitrarily selected class in the
only possible ambient way. This is the geometric input to transition continuity. -/
theorem chartClass_trans (c : X) {y z : X}
    (hy : y ∈ A.neighborhood c) (hz : z ∈ A.neighborhood c)
    (γ : Path y z) (hγ : ∀ t, γ t ∈ A.neighborhood c) :
    (A.chartClass b c y).trans (.mk γ) = A.chartClass b c z := by
  have hlocal := A.ambientPathThin c
    ((A.localPath c y hy).trans γ) (A.localPath c z hz)
    (trans_mem _ _ (A.localPath_mem c y hy) hγ) (A.localPath_mem c z hz)
  have hclasses := Path.Homotopic.Quotient.eq.mpr hlocal
  simp only [Path.Homotopic.Quotient.mk_trans] at hclasses
  simp only [chartClass, dite_eq_left hy, dite_eq_left hz,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.trans_assoc, hclasses]

/-- Actual fibre coordinate: finish the based path by reversing the chosen one. -/
def fiberEquiv (c y : X) : PathClassFiber b y ≃ PathClassFiber b b where
  toFun r := PathClassFiber.ofQuotient (r.toQuotient.trans (A.chartClass b c y).symm)
  invFun g := PathClassFiber.ofQuotient (g.toQuotient.trans (A.chartClass b c y))
  left_inv r := by
    apply PathClassFiber.ext
    change (r.toQuotient.trans (A.chartClass b c y).symm).trans
      (A.chartClass b c y) = r.toQuotient
    simp
  right_inv g := by
    apply PathClassFiber.ext
    change (g.toQuotient.trans (A.chartClass b c y)).trans
      (A.chartClass b c y).symm = g.toQuotient
    simp

/-- Literal dependent pair type; the topology is supplied by `prebundle`. -/
abbrev Total := Bundle.TotalSpace (PathClassFiber b b) (PathClassFiber b)

/-- Forward/inverse charts are genuine inverse functions before topology is
installed. Their source and target restrict them to the displayed open set. -/
def pretrivialization (c : X) :
    Bundle.Pretrivialization (PathClassFiber b b)
      (Bundle.TotalSpace.proj : Total b → X) where
  toFun e := (e.proj, A.fiberEquiv b c e.proj e.snd)
  invFun p := ⟨p.1, (A.fiberEquiv b c p.1).symm p.2⟩
  source := Bundle.TotalSpace.proj ⁻¹' A.neighborhood c
  target := A.neighborhood c ×ˢ univ
  map_source' e he := ⟨he, mem_univ _⟩
  map_target' p hp := hp.1
  left_inv' e _ := by
    cases e with | mk y r =>
    exact congrArg (Bundle.TotalSpace.mk y) ((A.fiberEquiv b c y).symm_apply_apply r)
  right_inv' p _ := Prod.ext rfl ((A.fiberEquiv b c p.1).apply_symm_apply p.2)
  open_target := (A.isOpen_neighborhood c).prod isOpen_univ
  baseSet := A.neighborhood c
  open_baseSet := A.isOpen_neighborhood c
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

/-- The transition from chart `d` to chart `c`, in chronological path notation. -/
def transitionClass (c d y : X) : PathClassFiber b b :=
  PathClassFiber.ofQuotient ((A.chartClass b d y).trans (A.chartClass b c y).symm)

omit [PathConnectedSpace X] in
private theorem class_trans_right_cancel {x y z : X}
    {p q : Path.Homotopic.Quotient x y} (r : Path.Homotopic.Quotient y z)
    (h : p.trans r = q.trans r) : p = q := by
  have h' := congrArg (fun s => s.trans r.symm) h
  simpa only [Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.trans_refl] using h'

/-- A path in the overlap leaves the transition class unchanged. -/
theorem transitionClass_eq_of_joinedIn (c d : X) {y z : X}
    (hy : y ∈ A.neighborhood d ∩ A.neighborhood c)
    (hz : z ∈ A.neighborhood d ∩ A.neighborhood c)
    (h : JoinedIn (A.neighborhood d ∩ A.neighborhood c) y z) :
    A.transitionClass b c d z = A.transitionClass b c d y := by
  let γ := h.somePath
  have hc := A.chartClass_trans b c hy.2 hz.2 γ (fun t => (h.somePath_mem t).2)
  have hd := A.chartClass_trans b d hy.1 hz.1 γ (fun t => (h.somePath_mem t).1)
  apply PathClassFiber.ext
  apply class_trans_right_cancel (A.chartClass b c z)
  have hcancel (w : X) :
      Path.Homotopic.Quotient.trans (A.transitionClass b c d w).toQuotient (A.chartClass b c w) =
        A.chartClass b d w := by
    simp [transitionClass]
  calc
    Path.Homotopic.Quotient.trans (A.transitionClass b c d z).toQuotient (A.chartClass b c z)
        = A.chartClass b d z := hcancel z
    _ = (A.chartClass b d y).trans (.mk γ) := hd.symm
    _ = (Path.Homotopic.Quotient.trans (A.transitionClass b c d y).toQuotient
          (A.chartClass b c y)).trans (.mk γ) := by rw [hcancel y]
    _ = Path.Homotopic.Quotient.trans (A.transitionClass b c d y).toQuotient
          ((A.chartClass b c y).trans (.mk γ)) :=
      Path.Homotopic.Quotient.trans_assoc _ _ _
    _ = Path.Homotopic.Quotient.trans (A.transitionClass b c d y).toQuotient
          (A.chartClass b c z) := by rw [hc]


variable [LocallyPathConnectedSpace X]

/-- Local constancy is proved on the actual overlap subtype using its open
pathcomponents; it is not an assumption about the chosen local paths. -/
theorem transitionClass_isLocallyConstant (c d : X) :
    IsLocallyConstant (fun y : ↥(A.neighborhood d ∩ A.neighborhood c) =>
      A.transitionClass b c d y.1) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro y
  let W := A.neighborhood d ∩ A.neighborhood c
  have hW : IsOpen W := (A.isOpen_neighborhood d).inter (A.isOpen_neighborhood c)
  refine ⟨Subtype.val ⁻¹' pathComponentIn W y.1,
    (hW.pathComponentIn y.1).preimage continuous_subtype_val,
    mem_pathComponentIn_self y.2, ?_⟩
  intro z hz
  exact A.transitionClass_eq_of_joinedIn b c d y.2 z.2 hz

omit [LocallyPathConnectedSpace X] in
/-- The full literal formula, valid even off the chart overlap. -/
theorem pretrivialization_transition_apply (c d : X) (p : X × PathClassFiber b b) :
    A.pretrivialization b c ((A.pretrivialization b d).toPartialEquiv.symm p) =
      (p.1, PathClassFiber.ofQuotient
        (p.2.toQuotient.trans (A.transitionClass b c d p.1).toQuotient)) := by
  apply Prod.ext
  · rfl
  · apply PathClassFiber.ext
    exact Path.Homotopic.Quotient.trans_assoc _ _ _

omit [LocallyPathConnectedSpace X] in
private theorem transition_domain (c d : X) :
    (A.pretrivialization b d).target ∩
        (A.pretrivialization b d).toPartialEquiv.symm ⁻¹'
          (A.pretrivialization b c).source =
      (A.neighborhood d ∩ A.neighborhood c) ×ˢ (univ : Set (PathClassFiber b b)) := by
  ext p
  change ((p.1 ∈ A.neighborhood d ∧ p.2 ∈ univ) ∧ p.1 ∈ A.neighborhood c) ↔
    ((p.1 ∈ A.neighborhood d ∧ p.1 ∈ A.neighborhood c) ∧ p.2 ∈ univ)
  simp

/-- The exact transition continuity field required by `FiberPrebundle`. -/
theorem continuousOn_pretrivialization_transition (c d : X) :
    ContinuousOn (A.pretrivialization b c ∘
        (A.pretrivialization b d).toPartialEquiv.symm)
      ((A.pretrivialization b d).target ∩
        (A.pretrivialization b d).toPartialEquiv.symm ⁻¹'
          (A.pretrivialization b c).source) := by
  rw [A.transition_domain b c d]
  have hδ : ContinuousOn (A.transitionClass b c d)
      (A.neighborhood d ∩ A.neighborhood c) :=
    continuousOn_iff_continuous_domRestrict.mpr
      (A.transitionClass_isLocallyConstant b c d).continuous
  have hδfst : ContinuousOn (fun p : X × PathClassFiber b b =>
      A.transitionClass b c d p.1)
      ((A.neighborhood d ∩ A.neighborhood c) ×ˢ univ) :=
    hδ.comp continuous_fst.continuousOn (fun _ hp => hp.1)
  have htrans : Continuous (fun p : PathClassFiber b b × PathClassFiber b b =>
      PathClassFiber.ofQuotient (p.1.toQuotient.trans p.2.toQuotient)) :=
    continuous_of_discreteTopology
  exact (continuous_fst.continuousOn.prodMk
    (htrans.comp_continuousOn (continuous_snd.continuousOn.prodMk hδfst))).congr
      (fun p _ => A.pretrivialization_transition_apply b c d p)

/-- Actual chart data supplies the topology; none is assumed on the total space. -/
def prebundle : FiberPrebundle (PathClassFiber b b) (PathClassFiber b) where
  pretrivializationAtlas := Set.range (A.pretrivialization b)
  pretrivializationAt := A.pretrivialization b
  mem_base_pretrivializationAt := A.mem_neighborhood
  pretrivialization_mem_atlas c := mem_range_self c
  continuous_trivChange := by
    rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
    exact A.continuousOn_pretrivialization_transition b c d
  totalSpaceMk_isInducing y := by
    change IsInducing (fun r : PathClassFiber b y => (y, A.fiberEquiv b y y r))
    exact Topology.isInducing_const_prod.mpr
      (A.fiberEquiv b y y).toHomeomorphOfDiscrete.isInducing

/-- The constructed literal projection is a genuine covering map under the
chart-generated topology. This conclusion alone does not assert universality. -/
theorem isCoveringMap_projection :
    letI := (A.prebundle b).totalSpaceTopology
    IsCoveringMap (Bundle.TotalSpace.proj : Total b → X) := by
  let := (A.prebundle b).totalSpaceTopology
  let := (A.prebundle b).toFiberBundle
  exact FiberBundle.isCoveringMap

omit [LocallyPathConnectedSpace X] in
/-- Surjectivity is separate from Mathlib's covering predicate. -/
theorem projection_surjective :
    Function.Surjective (Bundle.TotalSpace.proj : Total b → X) := by
  intro y
  exact ⟨⟨y, PathClassFiber.ofQuotient (.mk (PathConnectedSpace.somePath b y))⟩, rfl⟩

end PathThinNeighborhoods
end Topology
