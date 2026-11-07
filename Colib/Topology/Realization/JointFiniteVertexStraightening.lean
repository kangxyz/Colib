/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.EmbeddingFiniteVertexStraightening

/-!
# Joint finite vertex straightening for an actual embedding

Normalize the source while fixing every already-based source simplex. Its
actual image tracks agree with the stationary tracks on any based fixed target
family, because injectivity reflects each original source vertex. The joined
prescribed family is then extended by genuine finite simplex HEP to the whole
target support. Every repeated simplex and every face is indexed by actual map
equality, and source/target agreement holds at every original point and time.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u

namespace Convexity.StdSimplex
variable {Z : Type u} [TopologicalSpace Z]
variable {T F : FiniteSimplexFamily Z} (hT : T.FaceClosed) (hF : F.FaceClosed)
variable {z : Z} {N : ℕ}

/-- Adjoin stationary based simplices to existing compatible actual tracks. -/
def adjoinFixedFiniteFamily
    (R : PartialSimplexStraightening 1 z T F hT N)
    (hbased : ∀ d a, a ∈ F d → SimplexVerticesAt z a) :
    PartialSimplexStraightening 1 z (T.union F) F
      (FiniteSimplexFamily.faceClosed_union hT hF) N := by
  classical
  let L (d : ℕ) (a : {a // a ∈ (T.union F) d}) : C(StdSimplex ℝ (Fin (d + 1)) × I, Z) :=
    if ha : a.val ∈ T d then R.track d ⟨a.val, ha⟩ else
      ⟨fun q ↦ a.val q.1, by fun_prop⟩
  have hkeep (d : ℕ) (a : {a // a ∈ (T.union F) d}) (ha : a.val ∈ T d) :
      L d a = R.track d ⟨a.val, ha⟩ := by dsimp only [L]; rw [dite_eq_left ha]
  have hfix (d : ℕ) (a : {a // a ∈ (T.union F) d}) (ha : a.val ∈ F d) (q) (t) :
      L d a (q, t) = a.val q := by
    dsimp only [L]
    split_ifs with ht
    · exact R.stationary d _ ha q t
    · rfl
  exact {
    track := L
    bottom := by
      intro d a q
      dsimp only [L]
      split_ifs with ha
      · exact R.bottom d _ q
      · rfl
    stationary := hfix
    face := by
      intro d hd a i q t
      by_cases ha : a.val ∈ T (d + 1)
      · rw [hkeep _ a ha, R.face d hd]
        exact (congrArg (fun K ↦ K (q, t))
          (hkeep d ((FiniteSimplexFamily.faceClosed_union hT hF).face a i)
            (hT d a.val ha i))).symm
      · have haF : a.val ∈ F (d + 1) := (Finset.mem_union.mp a.property).resolve_left ha
        rw [hfix _ a haF]
        exact (hfix d ((FiniteSimplexFamily.faceClosed_union hT hF).face a i)
          (hF d a.val haF i) q t).symm
    top := by
      intro d hd hn a q
      by_cases ha : a.val ∈ T d
      · rw [hkeep _ a ha]
        exact R.top d hd hn _ q
      · have haF : a.val ∈ F d := (Finset.mem_union.mp a.property).resolve_left ha
        rw [hfix _ a haF]
        have he : d = 0 := by omega
        subst d
        exact ContinuousMap.congr_fun (hbased 0 a.val haF).zero q }

/-- Adjoining the fixed family leaves every prescribed original track unchanged. -/
theorem adjoinFixedFiniteFamily_track
    (R : PartialSimplexStraightening 1 z T F hT N)
    (hbased : ∀ d a, a ∈ F d → SimplexVerticesAt z a)
    (d : ℕ) (a : {a // a ∈ T d}) :
    (adjoinFixedFiniteFamily hT hF R hbased).track d
      ⟨a.val, by
        classical
        exact Finset.mem_union.mpr (Or.inl a.property)⟩ = R.track d a := by
  classical
  dsimp only [adjoinFixedFiniteFamily]
  rw [dite_eq_left a.property]

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Original target support together with the actual image support and the marked fixed family. -/
def jointTargetFamily (j : C(X, Y)) (S : FiniteSimplexFamily X)
    (B F : FiniteSimplexFamily Y) : FiniteSimplexFamily Y :=
  B.union ((imageFiniteFamily j S).union F)

/-- All original faces belong to the same merged target family. -/
theorem jointTargetFamily_faceClosed (j : C(X, Y))
    {S : FiniteSimplexFamily X} (hS : S.FaceClosed)
    {B F : FiniteSimplexFamily Y} (hB : B.FaceClosed) (hF : F.FaceClosed) :
    (jointTargetFamily j S B F).FaceClosed :=
  FiniteSimplexFamily.faceClosed_union hB
    (FiniteSimplexFamily.faceClosed_union (imageFiniteFamily_faceClosed j hS) hF)

/-- The original source simplex is retained under its actual target image. -/
def jointTargetSourceIndex (j : C(X, Y)) (S : FiniteSimplexFamily X)
    (B F : FiniteSimplexFamily Y) (d : ℕ) (a : {a // a ∈ S d}) :
    {a // a ∈ jointTargetFamily j S B F d} := by
  classical
  exact ⟨j.comp a.val, Finset.mem_union.mpr (Or.inr
    (Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨a.val, a.property, rfl⟩))))⟩

/-- The chosen image preimage is the original source simplex itself. -/
theorem imageFiniteFamilyPreimage_image (j : C(X, Y)) (hj : Function.Injective j)
    (S : FiniteSimplexFamily X) (d : ℕ) (a : {a // a ∈ S d}) :
    imageFiniteFamilyPreimage j S d
      ⟨j.comp a.val, by
        classical
        exact Finset.mem_image.mpr ⟨a.val, a.property, rfl⟩⟩ = a := by
  apply Subtype.ext
  apply comp_simplex_injective j hj d
  exact imageFiniteFamilyPreimage_comp j S d _

/-- Construct joint source and target tracks from connectedness and actual injectivity.
Every based marked target simplex is fixed, including its intersection with the source image. -/
theorem exists_joint_finite_vertex_straightening [PathConnectedSpace X] [PathConnectedSpace Y]
    (j : C(X, Y)) (hj : Function.Injective j) (x : X)
    (S : FiniteSimplexFamily X) (hS : S.FaceClosed)
    (B F : FiniteSimplexFamily Y) (hB : B.FaceClosed) (hF : F.FaceClosed)
    (hbased : ∀ d a, a ∈ F d → SimplexVerticesAt (j x) a) (N : ℕ) :
    ∃ R : PartialSimplexStraightening 1 x S (basedFiniteFamily x S) hS N,
      ∃ P : PartialSimplexStraightening 1 (j x) (jointTargetFamily j S B F) F
          (jointTargetFamily_faceClosed j hS hB hF) N,
        ∀ d, d < N → ∀ a : {a // a ∈ S d},
          P.track d (jointTargetSourceIndex j S B F d a) = j.comp (R.track d a) := by
  classical
  obtain ⟨R⟩ := exists_based_finite_vertex_straightening x S hS N
  let Rimage := imageFiniteVertexStraightening j hj x hS R F hbased
  let D := adjoinFixedFiniteFamily (imageFiniteFamily_faceClosed j hS) hF Rimage hbased
  have hinc (d : ℕ) : ((imageFiniteFamily j S).union F) d ⊆ jointTargetFamily j S B F d :=
    Finset.subset_union_right
  have hfixed (d : ℕ) : F d ⊆ ((imageFiniteFamily j S).union F) d :=
    Finset.subset_union_right
  obtain ⟨P, hP⟩ := exists_prescribed_finite_vertex_straightening
    (hS := jointTargetFamily_faceClosed j hS hB hF) hinc hfixed D
  refine ⟨R, P, ?_⟩
  intro d hd a
  let b : {b // b ∈ imageFiniteFamily j S d} :=
    ⟨j.comp a.val, Finset.mem_image.mpr ⟨a.val, a.property, rfl⟩⟩
  have he := hP d hd ⟨b.val, Finset.mem_union.mpr (Or.inl b.property)⟩
  refine he.trans ?_
  change (adjoinFixedFiniteFamily (imageFiniteFamily_faceClosed j hS) hF Rimage hbased).track
    d _ = _
  rw [adjoinFixedFiniteFamily_track]
  change j.comp (R.track d (imageFiniteFamilyPreimage j S d b)) = _
  rw [imageFiniteFamilyPreimage_image j hj S d a]

end Convexity.StdSimplex
