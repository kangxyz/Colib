/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.CubicalSubdivision.BoundaryLifting
public import Colib.Topology.CubicalSubdivision.StagePasting
public import Colib.Topology.CubicalSubdivision.OuterBoundary
public import Colib.Topology.CubicalSubdivision.FaceCover

/-! # Genuine locality of finite cube-boundary right lifting

A single finite affine grid is chosen for the given test map. Faces are filled
in dimension order, using the original boundary data on outer faces. Actual
quotient pasting retains all prescribed lower faces. No arbitrary inverse-image
subset is asserted to have HEP, and no continuous inverse family is chosen.


Implementation provenance:
`Quillen/Topology/CubicalSubdivision/LocalLifting.lean`
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
universe u v w

/-- The original map restricted over an actual target subset. -/
def restriction {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (U : Set B) : C({e : E // p e ∈ U}, U) where
  toFun e := ⟨p e.val,e.2⟩
  continuous_toFun := by fun_prop

/-- Strict finite cube-boundary lifting is local on an open target cover.
All maps and prescribed boundary values in the conclusion are the originals. -/
theorem BoundaryLifting.of_open_cover
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) {J : Type w} (U : J → Set B)
    (hU : ∀ j, IsOpen (U j)) (hcover : ∀ y : B, ∃ j, y ∈ U j)
    (hloc : ∀ j,BoundaryLifting (restriction p (U j))) : BoundaryLifting p := by
  intro n a b hab
  obtain ⟨m,hm⟩ := exists_grid_faces_subordinate n b U hU (fun x ↦ hcover (b x))
  choose chart hchart using hm
  have hstages : ∀ r : ℕ,∃ l : C(skeletonBelow n m r,E),
      (∀ x,p (l x) = b x.val) ∧
      ∀ (x : skeletonBelow n m r) (hx : x.val ∈ _root_.Cube.boundary (Fin n)),
        l x = a ⟨x.val,hx⟩ := by
    intro r
    induction r with
    | zero =>
      let : IsEmpty (skeletonBelow n m 0) := ⟨fun x ↦ by
        have hx := x.2
        simp only [skeletonBelow_zero,Set.mem_empty_iff_false] at hx⟩
      exact ⟨⟨isEmptyElim,continuous_of_discreteTopology⟩,fun x ↦ isEmptyElim x,
        fun x _ ↦ False.elim (isEmptyElim x : False)⟩
    | succ r ih =>
      obtain ⟨l,hlp,hla⟩ := ih
      have hfill : ∀ F : StageFace n m r,∃ c : C((Active F.1 → unitInterval),E),
          (∀ t : {t : Active F.1 → unitInterval // t ∈ _root_.Cube.boundary (Active F.1)},
            c t = l (stageBoundary F t)) ∧
          (∀ t,p (c t) = b (CubicalSubdivision.face F.1 t)) ∧
          ∀ (t : Active F.1 → unitInterval) (ht : CubicalSubdivision.face F.1 t ∈
            _root_.Cube.boundary (Fin n)),
            c t = a ⟨CubicalSubdivision.face F.1 t,ht⟩ := by
        intro F
        by_cases hF : OnOuterBoundary F.1
        · let c : C((Active F.1 → unitInterval),E) :=
            a.comp ⟨fun t ↦ ⟨CubicalSubdivision.face F.1 t,face_mem_outerBoundary F.1 hF t⟩,
              (CubicalSubdivision.face F.1).continuous.subtype_mk _⟩
          refine ⟨c,?_,?_,?_⟩
          · intro t
            exact (hla (stageBoundary F t) (face_mem_outerBoundary F.1 hF t)).symm
          · intro t
            exact hab ⟨CubicalSubdivision.face F.1 t,face_mem_outerBoundary F.1 hF t⟩
          · intro t ht
            rfl
        · let j := chart F.1
          let a' : C({t : Active F.1 → unitInterval // t ∈ _root_.Cube.boundary (Active F.1)},
              {e : E // p e ∈ U j}) := {
            toFun t := ⟨l (stageBoundary F t),by
              rw [hlp]
              exact hchart F.1 t⟩
            continuous_toFun := by fun_prop }
          let b' : C((Active F.1 → unitInterval),U j) := {
            toFun t := ⟨b (CubicalSubdivision.face F.1 t),hchart F.1 t⟩
            continuous_toFun := (b.continuous.comp (CubicalSubdivision.face
              F.1).continuous).subtype_mk _ }
          have hab' : ∀ t,restriction p (U j) (a' t) = b' t := by
            intro t
            exact Subtype.ext (hlp (stageBoundary F t))
          obtain ⟨c',hc',hp'⟩ := (hloc j).face F.1 a' b' hab'
          let c : C((Active F.1 → unitInterval),E) := ⟨fun t ↦ (c' t).val,by fun_prop⟩
          have hc (t : {t : Active F.1 → unitInterval // t ∈ _root_.Cube.boundary (Active F.1)}) :
              c t = l (stageBoundary F t) := congrArg Subtype.val (hc' t)
          refine ⟨c,hc,?_,?_⟩
          · intro t
            exact congrArg Subtype.val (ContinuousMap.congr_fun hp' t)
          · intro t ht
            have htb := face_preimage_outerBoundary_subset F.1 hF ht
            exact (hc ⟨t,htb⟩).trans (hla (stageBoundary F ⟨t,htb⟩) ht)
      choose f hf hp ha using hfill
      obtain ⟨g,hgl,hgf⟩ := exists_stage_paste n m r l f hf
      have hgp (x : skeleton n m r) : p (g x) = b x.val := by
        obtain ⟨z,rfl⟩ := stageProjection_surjective n m r x
        rcases z with y | ⟨F,t⟩
        · change p (g ⟨y.val,skeletonBelow_subset n m r y.2⟩) = b y.val
          rw [hgl]
          exact hlp y
        · change p (g ⟨CubicalSubdivision.face F.1 t,_⟩) = b (CubicalSubdivision.face F.1 t)
          rw [hgf]
          exact hp F t
      have hga (x : skeleton n m r) (hx : x.val ∈ _root_.Cube.boundary (Fin n)) :
          g x = a ⟨x.val,hx⟩ := by
        obtain ⟨z,rfl⟩ := stageProjection_surjective n m r x
        rcases z with y | ⟨F,t⟩
        · change g ⟨y.val,skeletonBelow_subset n m r y.2⟩ = a ⟨y.val,hx⟩
          rw [hgl]
          exact hla y hx
        · change g ⟨CubicalSubdivision.face F.1 t,_⟩ = a ⟨CubicalSubdivision.face F.1 t,hx⟩
          rw [hgf]
          exact ha F t hx
      let next : C(skeletonBelow n m (r+1),skeleton n m r) := {
        toFun x := ⟨x.val,by simpa only [skeletonBelow_succ] using x.2⟩
        continuous_toFun := by fun_prop }
      exact ⟨g.comp next,fun x ↦ hgp (next x),fun x hx ↦ hga (next x) hx⟩
  obtain ⟨l,hlp,hla⟩ := hstages (n+1)
  let top : C(Cube n,skeletonBelow n m (n+1)) := {
    toFun x := ⟨x,by rw [skeletonBelow_succ,skeleton_top]; trivial⟩
    continuous_toFun := by fun_prop }
  refine ⟨l.comp top,fun t ↦ hla (top t) t.2,?_⟩
  apply ContinuousMap.ext
  intro t
  exact hlp (top t)

end Topology.CubicalSubdivision
