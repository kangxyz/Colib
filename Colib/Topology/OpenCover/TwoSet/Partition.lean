/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyLifting.Collar.Cutoff
public import Colib.Topology.Homotopy.IntervalEndpoints
public import Colib.Topology.DeformationRetract.Basic

/-!
# The double cylinder of a partitioned two-open cover

The section of the collapse is constructed by actual cutoff extension.
It is glued on open sets, so no preservation of arbitrary quotient maps
under base change is used.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/OpenCover/TwoSet/Partition.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual maps and proofs
with native namespace and import ownership. -/
@[expose] public section

noncomputable section
open Topology
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
open unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace TopCat

/-- Concrete partition data subordinate to a two-open cover. -/
structure TwoOpenPartition (X : Type u) [TopologicalSpace X] where
  /-- The left member of the two-open cover of `X`. -/
  leftSet : Set X
  /-- The right member of the two-open cover of `X`. -/
  rightSet : Set X
  /-- The left cover set is open. -/
  left_open : IsOpen leftSet
  /-- The right cover set is open. -/
  right_open : IsOpen rightSet
  /-- The two open sets cover every point of `X`. -/
  cover : leftSet ∪ rightSet = Set.univ
  /-- An interval-valued continuous function selecting a point on each overlap cylinder. -/
  cutoff : C(X, I)
  /-- An auxiliary open set on which the cutoff is zero. -/
  zeroSet : Set X
  /-- An auxiliary open set on which the cutoff is one. -/
  oneSet : Set X
  /-- The region on which the cutoff is required to vanish is open. -/
  zero_open : IsOpen zeroSet
  /-- The region on which the cutoff is required to equal one is open. -/
  one_open : IsOpen oneSet
  /-- The right cover set and the zero region together cover `X`. -/
  right_zero_cover : rightSet ∪ zeroSet = Set.univ
  /-- The left cover set and the one region together cover `X`. -/
  left_one_cover : leftSet ∪ oneSet = Set.univ
  /-- The cutoff vanishes throughout the zero region. -/
  cutoff_zero : ∀ x ∈ zeroSet, cutoff x = 0
  /-- The cutoff equals one throughout the one region. -/
  cutoff_one : ∀ x ∈ oneSet, cutoff x = 1

namespace TwoOpenPartition
variable {X : Type u} [TopologicalSpace X] (P : TwoOpenPartition X)

/-- The left open set, regarded as a subspace of `X`. -/
abbrev Left := P.leftSet
/-- The right open set, regarded as a subspace of `X`. -/
abbrev Right := P.rightSet
/-- The intersection of the two cover sets, with its subspace topology. -/
abbrev Overlap := P.leftSet ∩ P.rightSet

/-- The two endpoint copies of the overlap map to the two open sets. -/
def endMap : TopCat.of (P.Overlap ⊕ P.Overlap) ⟶ TopCat.of (P.Left ⊕ P.Right) :=
  TopCat.ofHom ⟨Sum.elim (fun a ↦ Sum.inl ⟨a.1, a.2.1⟩)
    (fun a ↦ Sum.inr ⟨a.1, a.2.2⟩), continuous_sum_dom.mpr ⟨by fun_prop, by fun_prop⟩⟩

variable {D : TopCat.{u}}
  {l : TopCat.of P.Overlap ⊗ TopCat.I ⟶ D}
  {e : TopCat.of (P.Left ⊕ P.Right) ⟶ D}
  (sq : IsPushout (TopCat.intervalEndpoints (TopCat.of P.Overlap)) P.endMap l e)

/-- Collapse every interval to its common point of the cover. -/
def collapse : D ⟶ TopCat.of X := sq.desc
  (TopCat.ofHom ⟨fun z ↦ z.1.1, by fun_prop⟩)
  (TopCat.ofHom ⟨Sum.elim Subtype.val Subtype.val,
    continuous_sum_dom.mpr ⟨continuous_subtype_val, continuous_subtype_val⟩⟩)
  (by ext a; cases a <;> rfl)

@[simp] theorem collapse_cylinder (a : P.Overlap) (t : I) :
    collapse P sq (l (a, ULift.up t)) = a.1 :=
  ConcreteCategory.congr_hom (sq.inl_desc _ _ _) (a, ULift.up t)
@[simp] theorem collapse_left (x : P.Left) : collapse P sq (e (Sum.inl x)) = x.1 :=
  ConcreteCategory.congr_hom (sq.inr_desc _ _ _) (Sum.inl x)
@[simp] theorem collapse_right (x : P.Right) : collapse P sq (e (Sum.inr x)) = x.1 :=
  ConcreteCategory.congr_hom (sq.inr_desc _ _ _) (Sum.inr x)

include sq in
theorem cylinder_zero (a : P.Overlap) : l (a, ULift.up (0 : I)) = e (Sum.inl ⟨a.1, a.2.1⟩) :=
  ConcreteCategory.congr_hom sq.w (Sum.inl a)
include sq in
theorem cylinder_one (a : P.Overlap) : l (a, ULift.up (1 : I)) = e (Sum.inr ⟨a.1, a.2.2⟩) :=
  ConcreteCategory.congr_hom sq.w (Sum.inr a)

/-- The overlap viewed as a subset of the left chart, where its cylinder path is defined. -/
def leftDomain : Set P.Left := {x | x.1 ∈ P.rightSet}
/-- The zero region restricted to the left chart, where the extended path is stationary. -/
def leftZero : Set P.Left := {x | x.1 ∈ P.zeroSet}
/-- The overlap viewed as a subset of the right chart, where its reversed cylinder path is
defined. -/
def rightDomain : Set P.Right := {x | x.1 ∈ P.leftSet}
/-- The one region restricted to the right chart, where the reflected cutoff vanishes. -/
def rightZero : Set P.Right := {x | x.1 ∈ P.oneSet}

theorem leftDomain_open : IsOpen P.leftDomain := P.right_open.preimage continuous_subtype_val
theorem leftZero_open : IsOpen P.leftZero := P.zero_open.preimage continuous_subtype_val
theorem rightDomain_open : IsOpen P.rightDomain := P.left_open.preimage continuous_subtype_val
theorem rightZero_open : IsOpen P.rightZero := P.one_open.preimage continuous_subtype_val

theorem left_cover : P.leftDomain ∪ P.leftZero = Set.univ := by
  ext x
  have hx : x.1 ∈ P.rightSet ∪ P.zeroSet := by rw [P.right_zero_cover]; trivial
  exact iff_of_true hx (Set.mem_univ _)
theorem right_cover : P.rightDomain ∪ P.rightZero = Set.univ := by
  ext x
  have hx : x.1 ∈ P.leftSet ∪ P.oneSet := by rw [P.left_one_cover]; trivial
  exact iff_of_true hx (Set.mem_univ _)

/-- Restrict the cutoff to the left chart to control extension of its cylinder path. -/
def leftCutoff : C(P.Left, I) := ⟨fun x ↦ P.cutoff x.1, by fun_prop⟩
/-- Restrict the reflected cutoff to the right chart to control its reversed cylinder path. -/
def rightCutoff : C(P.Right, I) := ⟨fun x ↦ σ (P.cutoff x.1), by fun_prop⟩
theorem leftCutoff_zero : ∀ x ∈ P.leftZero, P.leftCutoff x = 0 := fun x hx ↦ P.cutoff_zero x.1 hx
theorem rightCutoff_zero : ∀ x ∈ P.rightZero, P.rightCutoff x = 0 := by
  intro x hx
  change σ (P.cutoff x.1) = 0
  rw [P.cutoff_one x.1 hx, symm_one]

/-- The inclusion of the left chart into the left endpoint piece of the double cylinder. -/
def leftInitial : C(P.Left, D) := ⟨fun x ↦ e (Sum.inl x), by fun_prop⟩
/-- The inclusion of the right chart into the right endpoint piece of the double cylinder. -/
def rightInitial : C(P.Right, D) := ⟨fun x ↦ e (Sum.inr x), by fun_prop⟩
/-- The cylinder path on the left overlap, running from interval coordinate zero to one. -/
def leftLocal : C(I × P.leftDomain, D) :=
  ⟨fun z ↦ l (⟨z.2.1.1, z.2.1.2, z.2.2⟩, ULift.up z.1), by fun_prop⟩
/-- The cylinder path on the right overlap with reversed interval coordinate, starting at the
right endpoint piece. -/
def rightLocal : C(I × P.rightDomain, D) :=
  ⟨fun z ↦ l (⟨z.2.1.1, z.2.2, z.2.1.2⟩, ULift.up (σ z.1)), by fun_prop⟩
include sq in
theorem leftLocal_zero (x : P.leftDomain) : leftLocal P (l := l) (0, x) = leftInitial P (e := e)
    x.1 :=
  cylinder_zero P sq ⟨x.1.1, x.1.2, x.2⟩
include sq in
theorem rightLocal_zero (x : P.rightDomain) : rightLocal P (l := l) (0, x) = rightInitial P (e
    := e) x.1 := by
  simpa only [rightLocal, rightInitial, ContinuousMap.coe_mk, symm_zero] using
    cylinder_one P sq ⟨x.1.1, x.2, x.1.2⟩

/-- A continuous path from each left chart point toward the cutoff section. -/
def leftPath : C(I × P.Left, D) := cutoffLift P.leftDomain P.leftZero
  P.leftDomain_open P.leftZero_open P.left_cover P.leftCutoff P.leftCutoff_zero
  (leftInitial P) (leftLocal P) (leftLocal_zero P sq)
/-- A continuous path from each right chart point toward the same section. -/
def rightPath : C(I × P.Right, D) := cutoffLift P.rightDomain P.rightZero
  P.rightDomain_open P.rightZero_open P.right_cover P.rightCutoff P.rightCutoff_zero
  (rightInitial P) (rightLocal P) (rightLocal_zero P sq)

@[simp] theorem leftPath_zero (x : P.Left) : leftPath P sq (0, x) = e (Sum.inl x) :=
  cutoffLift_zero _ _ _ _ _ _ _ _ _ _ x
@[simp] theorem rightPath_zero (x : P.Right) : rightPath P sq (0, x) = e (Sum.inr x) :=
  cutoffLift_zero _ _ _ _ _ _ _ _ _ _ x

theorem leftPath_overlap (t : I) (a : P.Overlap) :
    leftPath P sq (t, ⟨a.1, a.2.1⟩) = l (a, ULift.up (t * P.cutoff a.1)) :=
  cutoffLift_apply_of_mem P.leftDomain P.leftZero P.leftDomain_open P.leftZero_open
    P.left_cover P.leftCutoff P.leftCutoff_zero (leftInitial P) (leftLocal P)
    (leftLocal_zero P sq) t ⟨a.1, a.2.1⟩ a.2.2
theorem rightPath_overlap (t : I) (a : P.Overlap) :
    rightPath P sq (t, ⟨a.1, a.2.2⟩) = l (a, ULift.up (σ (t * σ (P.cutoff a.1)))) :=
  cutoffLift_apply_of_mem P.rightDomain P.rightZero P.rightDomain_open P.rightZero_open
    P.right_cover P.rightCutoff P.rightCutoff_zero (rightInitial P) (rightLocal P)
    (rightLocal_zero P sq) t ⟨a.1, a.2.2⟩ a.2.1

/-- The actual maps on the two open sets used to construct the section. -/
def coverSet (b : Bool) : Set X := if b then P.leftSet else P.rightSet

/-- The local section on each cover set, obtained by evaluating its cutoff path at time one;
these maps are glued to form `sectionMap`. -/
def sectionParts (b : Bool) : C(P.coverSet b, D) := by
  cases b
  · exact homotopyTimeSlice (rightPath P sq) 1
  · exact homotopyTimeSlice (leftPath P sq) 1

theorem sectionParts_agree (b c : Bool) (x : X)
    (hb : x ∈ P.coverSet b)
    (hc : x ∈ P.coverSet c) :
    sectionParts P sq b ⟨x, hb⟩ = sectionParts P sq c ⟨x, hc⟩ := by
  cases b <;> cases c
  · rfl
  · change rightPath P sq (1, ⟨x, hb⟩) = leftPath P sq (1, ⟨x, hc⟩)
    rw [rightPath_overlap P sq 1 ⟨x, hc, hb⟩, leftPath_overlap P sq 1 ⟨x, hc, hb⟩]
    simp
  · change leftPath P sq (1, ⟨x, hb⟩) = rightPath P sq (1, ⟨x, hc⟩)
    rw [leftPath_overlap P sq 1 ⟨x, hb, hc⟩, rightPath_overlap P sq 1 ⟨x, hb, hc⟩]
    simp
  · rfl

theorem coverNeighborhood (x : X) :
    ∃ b : Bool, P.coverSet b ∈ nhds x := by
  have hx : x ∈ P.leftSet ∪ P.rightSet := by rw [P.cover]; trivial
  rcases hx with hx | hx
  · exact ⟨true, P.left_open.mem_nhds hx⟩
  · exact ⟨false, P.right_open.mem_nhds hx⟩

/-- A continuous section of the double-cylinder collapse. -/
def sectionMap : C(X, D) := ContinuousMap.liftCover
  P.coverSet
  (sectionParts P sq) (sectionParts_agree P sq) P.coverNeighborhood

theorem sectionMap_left (x : P.Left) : sectionMap P sq x.1 = leftPath P sq (1, x) :=
  ContinuousMap.liftCover_coe (hS := P.coverNeighborhood) (i := true) x
theorem sectionMap_right (x : P.Right) : sectionMap P sq x.1 = rightPath P sq (1, x) :=
  ContinuousMap.liftCover_coe (hS := P.coverNeighborhood) (i := false) x

theorem sectionMap_overlap (a : P.Overlap) :
    sectionMap P sq a.1 = l (a, ULift.up (P.cutoff a.1)) := by
  rw [sectionMap_left P sq ⟨a.1, a.2.1⟩, leftPath_overlap]
  simp

theorem collapse_leftPath (t : I) (x : P.Left) :
    collapse P sq (leftPath P sq (t, x)) = x.1 := by
  exact cutoffLift_property P.leftDomain P.leftZero P.leftDomain_open P.leftZero_open
    P.left_cover P.leftCutoff P.leftCutoff_zero (leftInitial P) (leftLocal P)
    (leftLocal_zero P sq) (fun _ x d ↦ collapse P sq d = x.1)
    (fun _ a ↦ collapse_cylinder P sq _ _) (fun _ x _ ↦ collapse_left P sq x) t x

theorem collapse_rightPath (t : I) (x : P.Right) :
    collapse P sq (rightPath P sq (t, x)) = x.1 := by
  exact cutoffLift_property P.rightDomain P.rightZero P.rightDomain_open P.rightZero_open
    P.right_cover P.rightCutoff P.rightCutoff_zero (rightInitial P) (rightLocal P)
    (rightLocal_zero P sq) (fun _ x d ↦ collapse P sq d = x.1)
    (fun _ a ↦ collapse_cylinder P sq _ _) (fun _ x _ ↦ collapse_right P sq x) t x

@[simp] theorem collapse_sectionMap (x : X) : collapse P sq (sectionMap P sq x) = x := by
  have hx : x ∈ P.leftSet ∪ P.rightSet := by rw [P.cover]; trivial
  rcases hx with hx | hx
  · rw [sectionMap_left P sq ⟨x, hx⟩]
    exact collapse_leftPath P sq 1 ⟨x, hx⟩
  · rw [sectionMap_right P sq ⟨x, hx⟩]
    exact collapse_rightPath P sq 1 ⟨x, hx⟩

/-- Where the partition vanishes, the left path and section are exactly stationary. -/
theorem leftPath_of_cutoff_zero (t : I) (x : P.Left) (hx : P.cutoff x.1 = 0) :
    leftPath P sq (t, x) = e (Sum.inl x) :=
  cutoffLift_apply_of_zero P.leftDomain P.leftZero P.leftDomain_open P.leftZero_open
    P.left_cover P.leftCutoff P.leftCutoff_zero (leftInitial P) (leftLocal P)
    (leftLocal_zero P sq) t x hx

/-- Where the partition is one, the right path and section are exactly stationary. -/
theorem rightPath_of_cutoff_one (t : I) (x : P.Right) (hx : P.cutoff x.1 = 1) :
    rightPath P sq (t, x) = e (Sum.inr x) := by
  apply cutoffLift_apply_of_zero P.rightDomain P.rightZero P.rightDomain_open P.rightZero_open
    P.right_cover P.rightCutoff P.rightCutoff_zero (rightInitial P) (rightLocal P)
    (rightLocal_zero P sq) t x
  change σ (P.cutoff x.1) = 0
  rw [hx, symm_one]

theorem sectionMap_of_cutoff_zero (x : P.Left) (hx : P.cutoff x.1 = 0) :
    sectionMap P sq x.1 = e (Sum.inl x) :=
  (sectionMap_left P sq x).trans (leftPath_of_cutoff_zero P sq 1 x hx)

theorem sectionMap_of_cutoff_one (x : P.Right) (hx : P.cutoff x.1 = 1) :
    sectionMap P sq x.1 = e (Sum.inr x) :=
  (sectionMap_right P sq x).trans (rightPath_of_cutoff_one P sq 1 x hx)

/-- The straight interval homotopy on the central cylinder. -/
def cylinderHomotopy : (TopCat.of P.Overlap ⊗ TopCat.I) ⊗ TopCat.I ⟶ D := by
  apply TopCat.ofHom
  change C((P.Overlap × ULift.{u} I) × ULift.{u} I, D)
  exact ⟨fun z ↦ l (z.1.1,
    ULift.up (Set.Icc.convexComb (P.cutoff z.1.1.1) z.1.2.down z.2.down)), by
      unfold Set.Icc.convexComb
      fun_prop⟩

/-- Reverse the two cutoff paths on the endpoint pieces. -/
def endHomotopy : TopCat.of (P.Left ⊕ P.Right) ⊗ TopCat.I ⟶ D := by
  let F : C((P.Left × ULift.{u} I) ⊕ (P.Right × ULift.{u} I), D) :=
    ⟨Sum.elim (fun z ↦ leftPath P sq (σ z.2.down, z.1))
      (fun z ↦ rightPath P sq (σ z.2.down, z.1)),
      continuous_sum_dom.mpr ⟨by fun_prop, by fun_prop⟩⟩
  let E : (P.Left ⊕ P.Right) × ULift.{u} I ≃ₜ
      (P.Left × ULift.{u} I) ⊕ (P.Right × ULift.{u} I) := Homeomorph.sumProdDistrib
  apply TopCat.ofHom
  change C((P.Left ⊕ P.Right) × ULift.{u} I, D)
  exact F.comp (E : C(_, _))

theorem homotopy_square :
    (TopCat.intervalEndpoints (TopCat.of P.Overlap) ▷ TopCat.I) ≫ cylinderHomotopy P (l := l) =
      (P.endMap ▷ TopCat.I) ≫ endHomotopy P sq := by
  apply ConcreteCategory.hom_ext
  rintro ⟨a | a, t⟩
  · change l (a, ULift.up (Set.Icc.convexComb (P.cutoff a.1) 0 t.down)) =
      leftPath P sq (σ t.down, ⟨a.1, a.2.1⟩)
    rw [leftPath_overlap]
    apply congrArg (fun v : I ↦ l (a, ULift.up v))
    apply Subtype.ext
    change (1 - (t.down : ℝ)) * (P.cutoff a.1 : ℝ) + (t.down : ℝ) * 0 = _
    simp
  · change l (a, ULift.up (Set.Icc.convexComb (P.cutoff a.1) 1 t.down)) =
      rightPath P sq (σ t.down, ⟨a.1, a.2.2⟩)
    rw [rightPath_overlap]
    apply congrArg (fun v : I ↦ l (a, ULift.up v))
    apply Subtype.ext
    change (1 - (t.down : ℝ)) * (P.cutoff a.1 : ℝ) + (t.down : ℝ) * 1 =
      1 - ((1 - (t.down : ℝ)) * (1 - (P.cutoff a.1 : ℝ)))
    ring

/-- The actual homotopy on the entire double mapping cylinder. -/
def sectionHomotopyCylinder : D ⊗ TopCat.I ⟶ D :=
  (sq.map (tensorRight TopCat.I)).desc (cylinderHomotopy P) (endHomotopy P sq)
    (homotopy_square P sq)

theorem sectionHomotopyCylinder_cylinder (a : P.Overlap) (t s : I) :
    sectionHomotopyCylinder P sq (l (a, ULift.up t), ULift.up s) =
      l (a, ULift.up (Set.Icc.convexComb (P.cutoff a.1) t s)) :=
  ConcreteCategory.congr_hom ((sq.map (tensorRight TopCat.I)).inl_desc _ _ _)
    ((a, ULift.up t), ULift.up s)
theorem sectionHomotopyCylinder_left (x : P.Left) (s : I) :
    sectionHomotopyCylinder P sq (e (Sum.inl x), ULift.up s) = leftPath P sq (σ s, x) :=
  ConcreteCategory.congr_hom ((sq.map (tensorRight TopCat.I)).inr_desc _ _ _)
    (Sum.inl x, ULift.up s)
theorem sectionHomotopyCylinder_right (x : P.Right) (s : I) :
    sectionHomotopyCylinder P sq (e (Sum.inr x), ULift.up s) = rightPath P sq (σ s, x) :=
  ConcreteCategory.congr_hom ((sq.map (tensorRight TopCat.I)).inr_desc _ _ _)
    (Sum.inr x, ULift.up s)

theorem sectionHomotopyCylinder_zero : TopCat.ι₀ ≫ sectionHomotopyCylinder P sq =
    collapse P sq ≫ TopCat.ofHom (sectionMap P sq) := by
  apply sq.hom_ext
  · apply ConcreteCategory.hom_ext
    intro ⟨a, t⟩
    change sectionHomotopyCylinder P sq (l (a, t), ULift.up 0) =
      sectionMap P sq (collapse P sq (l (a, t)))
    erw [sectionHomotopyCylinder_cylinder P sq a t.down 0, Set.Icc.convexComb_zero,
      collapse_cylinder P sq a t.down, sectionMap_overlap]
  · apply ConcreteCategory.hom_ext
    intro x
    cases x with
    | inl x =>
      change sectionHomotopyCylinder P sq (e (Sum.inl x), ULift.up 0) =
        sectionMap P sq (collapse P sq (e (Sum.inl x)))
      rw [sectionHomotopyCylinder_left, symm_zero, collapse_left, sectionMap_left]
    | inr x =>
      change sectionHomotopyCylinder P sq (e (Sum.inr x), ULift.up 0) =
        sectionMap P sq (collapse P sq (e (Sum.inr x)))
      rw [sectionHomotopyCylinder_right, symm_zero, collapse_right, sectionMap_right]

theorem sectionHomotopyCylinder_one : TopCat.ι₁ ≫ sectionHomotopyCylinder P sq = 𝟙 D := by
  apply sq.hom_ext
  · apply ConcreteCategory.hom_ext
    intro ⟨a, t⟩
    change sectionHomotopyCylinder P sq (l (a, t), ULift.up 1) = l (a, t)
    erw [sectionHomotopyCylinder_cylinder P sq a t.down 1, Set.Icc.convexComb_one]
    cases t
    rfl
  · apply ConcreteCategory.hom_ext
    intro x
    cases x with
    | inl x =>
      change sectionHomotopyCylinder P sq (e (Sum.inl x), ULift.up 1) = e (Sum.inl x)
      rw [sectionHomotopyCylinder_left, symm_one, leftPath_zero]
    | inr x =>
      change sectionHomotopyCylinder P sq (e (Sum.inr x), ULift.up 1) = e (Sum.inr x)
      rw [sectionHomotopyCylinder_right, symm_one, rightPath_zero]

/-- The inverse homotopy keeps its underlying point of the covered space fixed. -/
theorem sectionHomotopyCylinder_over : sectionHomotopyCylinder P sq ≫ collapse P sq =
    fst D TopCat.I ≫ collapse P sq := by
  apply (sq.map (tensorRight TopCat.I)).hom_ext
  · apply ConcreteCategory.hom_ext
    intro ⟨⟨a, t⟩, s⟩
    change collapse P sq (sectionHomotopyCylinder P sq (l (a, t), s)) = collapse P sq (l (a, t))
    erw [sectionHomotopyCylinder_cylinder P sq a t.down s.down,
      collapse_cylinder, collapse_cylinder P sq a t.down]
  · apply ConcreteCategory.hom_ext
    intro ⟨x, s⟩
    cases x with
    | inl x =>
      change collapse P sq (sectionHomotopyCylinder P sq (e (Sum.inl x), s)) =
        collapse P sq (e (Sum.inl x))
      erw [sectionHomotopyCylinder_left P sq x s.down, collapse_leftPath, collapse_left]
    | inr x =>
      change collapse P sq (sectionHomotopyCylinder P sq (e (Sum.inr x), s)) =
        collapse P sq (e (Sum.inr x))
      erw [sectionHomotopyCylinder_right P sq x s.down, collapse_rightPath, collapse_right]

/-- The canonical double-cylinder collapse of a partitioned two-open
cover is an actual homotopy equivalence. -/
def collapseHomotopyEquiv : ContinuousMap.HomotopyEquiv D X where
  toFun := (collapse P sq).hom
  invFun := sectionMap P sq
  left_inv := ⟨TopCat.homotopyOfCylinder (sectionHomotopyCylinder P sq)
    (sectionHomotopyCylinder_zero P sq) (sectionHomotopyCylinder_one P sq)⟩
  right_inv := ⟨(ContinuousMap.Homotopy.refl (ContinuousMap.id X)).cast
    (by ext x; exact (collapse_sectionMap P sq x).symm) rfl⟩

@[simp] theorem collapseHomotopyEquiv_toFun : (collapseHomotopyEquiv P sq).toFun =
    (collapse P sq).hom := rfl

end TwoOpenPartition
end TopCat
