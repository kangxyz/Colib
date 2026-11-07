/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.CubicalSubdivision.IncidentCharts
public import Colib.Topology.CubicalSubdivision.StagePasting
public import Colib.Topology.CubicalSubdivision.OuterBoundary

/-! # Finite grid lifting with every incident face constraint

Actual cells are filled in dimension order and pasted through the proved
quotient skeleton. The invariant retains membership in every containing
face's source constraint, rather than a single arbitrarily selected chart.
The boundary and the displayed map to the target are retained exactly.


Implementation provenance:
`Quillen/Topology/CubicalSubdivision/ControlledLifting.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
namespace Topology.CubicalSubdivision
universe u v

/-- Exact finite-cell lifting assembles globally while preserving every
incident face constraint and the whole originally prescribed boundary.
The local input is only filling each actual face with its full boundary. -/
theorem exists_controlled_grid_lift (n m : ℕ)
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (a : C({x : Cube n // x ∈ _root_.Cube.boundary (Fin n)}, E))
    (b : C(Cube n, B)) (hab : ∀ x, p (a x) = b x.val)
    (K : FaceIndex n m → Set E)
    (hK : ∀ F G, faceSet F ⊆ faceSet G → K F ⊆ K G)
    (haK : ∀ F (x : {x : Cube n // x ∈ _root_.Cube.boundary (Fin n)}),
      x.val ∈ faceSet F → a x ∈ K F)
    (hfill : ∀ F : FaceIndex n m,
      ∀ c : C({t : Active F → unitInterval // t ∈ _root_.Cube.boundary (Active F)},E),
        (∀ t,c t ∈ K F) → (∀ t,p (c t) = b (face F t.val)) →
        ∃ d : C((Active F → unitInterval),E),
          (∀ t : {t : Active F → unitInterval // t ∈ _root_.Cube.boundary (Active F)},d t.val =
            c t) ∧
          (∀ t,p (d t) = b (face F t)) ∧ (∀ t,d t ∈ K F)) :
    ∃ l : C(Cube n,E),
      (∀ x : {x : Cube n // x ∈ _root_.Cube.boundary (Fin n)},l x.val = a x) ∧
      p.comp l = b ∧ ∀ (F : FaceIndex n m) (t : Active F → unitInterval),l (face F t) ∈ K F := by
  have hstages : ∀ r : ℕ,∃ l : C(skeletonBelow n m r,E),
      (∀ x,p (l x) = b x.val) ∧
      (∀ (x : skeletonBelow n m r) (hx : x.val ∈ _root_.Cube.boundary (Fin n)),
        l x = a ⟨x.val,hx⟩) ∧
      ∀ (G : FaceIndex n m) (x : skeletonBelow n m r),x.val ∈ faceSet G → l x ∈ K G := by
    intro r
    induction r with
    | zero =>
      let : IsEmpty (skeletonBelow n m 0) := ⟨fun x ↦ by
        have hx := x.2
        simp only [skeletonBelow_zero,Set.mem_empty_iff_false] at hx⟩
      exact ⟨⟨isEmptyElim,continuous_of_discreteTopology⟩,fun x ↦ isEmptyElim x,
        fun x _ ↦ False.elim (isEmptyElim x : False),fun _ x _ ↦ isEmptyElim x⟩
    | succ r ih =>
      obtain ⟨l,hlp,hla,hlK⟩ := ih
      have hfaces : ∀ F : StageFace n m r,∃ c : C((Active F.1 → unitInterval),E),
          (∀ t : {t : Active F.1 → unitInterval // t ∈ _root_.Cube.boundary (Active F.1)},
            c t.val = l (stageBoundary F t)) ∧
          (∀ t,p (c t) = b (face F.1 t)) ∧
          (∀ (t : Active F.1 → unitInterval) (ht : face F.1 t ∈ _root_.Cube.boundary (Fin n)),
            c t = a ⟨face F.1 t,ht⟩) ∧ (∀ t,c t ∈ K F.1) := by
        intro F
        by_cases hF : OnOuterBoundary F.1
        · let c : C((Active F.1 → unitInterval),E) :=
            a.comp ⟨fun t ↦ ⟨face F.1 t,face_mem_outerBoundary F.1 hF t⟩,
              (face F.1).continuous.subtype_mk _⟩
          refine ⟨c,?_,?_,?_,?_⟩
          · intro t
            exact (hla (stageBoundary F t) (face_mem_outerBoundary F.1 hF t.val)).symm
          · intro t
            exact hab ⟨face F.1 t,face_mem_outerBoundary F.1 hF t⟩
          · intro t ht
            rfl
          · intro t
            exact haK F.1 ⟨face F.1 t,face_mem_outerBoundary F.1 hF t⟩ ⟨t,rfl⟩
        · let c : C({t : Active F.1 → unitInterval // t ∈ _root_.Cube.boundary (Active F.1)},E) :=
            l.comp (stageBoundary F)
          obtain ⟨d,hd,hdp,hdK⟩ := hfill F.1 c
            (fun t ↦ hlK F.1 (stageBoundary F t) ⟨t.val,rfl⟩)
            (fun t ↦ hlp (stageBoundary F t))
          refine ⟨d,hd,hdp,?_,hdK⟩
          intro t ht
          have htb := face_preimage_outerBoundary_subset F.1 hF ht
          exact (hd ⟨t,htb⟩).trans (hla (stageBoundary F ⟨t,htb⟩) ht)
      choose f hf hp ha hk using hfaces
      obtain ⟨g,hgl,hgf⟩ := exists_stage_paste n m r l f hf
      have hgp (x : skeleton n m r) : p (g x) = b x.val := by
        obtain ⟨z,rfl⟩ := stageProjection_surjective n m r x
        rcases z with y | ⟨F,t⟩
        · change p (g ⟨y.val,skeletonBelow_subset n m r y.2⟩) = b y.val
          rw [hgl]
          exact hlp y
        · change p (g ⟨face F.1 t,_⟩) = b (face F.1 t)
          rw [hgf]
          exact hp F t
      have hga (x : skeleton n m r) (hx : x.val ∈ _root_.Cube.boundary (Fin n)) :
          g x = a ⟨x.val,hx⟩ := by
        obtain ⟨z,rfl⟩ := stageProjection_surjective n m r x
        rcases z with y | ⟨F,t⟩
        · change g ⟨y.val,skeletonBelow_subset n m r y.2⟩ = a ⟨y.val,hx⟩
          rw [hgl]
          exact hla y hx
        · change g ⟨face F.1 t,_⟩ = a ⟨face F.1 t,hx⟩
          rw [hgf]
          exact ha F t hx
      have hgK (G : FaceIndex n m) (x : skeleton n m r) (hx : x.val ∈ faceSet G) : g x ∈ K G := by
        obtain ⟨z,rfl⟩ := stageProjection_surjective n m r x
        rcases z with y | ⟨F,t⟩
        · change g ⟨y.val,skeletonBelow_subset n m r y.2⟩ ∈ K G
          rw [hgl]
          exact hlK G y hx
        · change g ⟨face F.1 t,_⟩ ∈ K G
          rw [hgf]
          rcases face_boundary_or_subset_of_mem F.1 G t hx with ht | hFG
          · rw [hf F ⟨t,ht⟩]
            exact hlK G (stageBoundary F ⟨t,ht⟩) hx
          · exact hK F.1 G hFG (hk F t)
      let next : C(skeletonBelow n m (r+1),skeleton n m r) := {
        toFun x := ⟨x.val,by simpa only [skeletonBelow_succ] using x.2⟩
        continuous_toFun := by fun_prop }
      exact ⟨g.comp next,fun x ↦ hgp (next x),fun x hx ↦ hga (next x) hx,
        fun G x hx ↦ hgK G (next x) hx⟩
  obtain ⟨l,hlp,hla,hlK⟩ := hstages (n+1)
  let top : C(Cube n,skeletonBelow n m (n+1)) := {
    toFun x := ⟨x,by rw [skeletonBelow_succ,skeleton_top]; trivial⟩
    continuous_toFun := by fun_prop }
  refine ⟨l.comp top,fun x ↦ hla (top x.val) x.2,?_,?_⟩
  · exact ContinuousMap.ext (fun x ↦ hlp (top x))
  · intro F t
    exact hlK F (top (face F t)) ⟨t,rfl⟩

end Topology.CubicalSubdivision
