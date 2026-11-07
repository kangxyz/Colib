/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.FiniteVertexStraightening
public import Mathlib.Topology.Connected.PathConnected

/-!
# Extend actual prescribed finite vertex-straightening tracks

An existing face-compatible homotopy on a finite face-closed subfamily extends
to a larger finite face-closed family, with every prescribed point and time
unchanged. Only vertices are collapsed. Higher dimensions use genuine simplex
boundary HEP and require no homotopy-group vanishing. Equal singular maps are
the same index in both families.
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
variable {S T F : FiniteSimplexFamily Z} {hS : S.FaceClosed} {hT : T.FaceClosed}
variable {z : Z} {N : ℕ}

/-- The same original simplex viewed in the larger actual family. -/
def finiteFamilyInclusion (hTS : ∀ d, T d ⊆ S d) (d : ℕ) (a : {a // a ∈ T d}) :
    {a // a ∈ S d} := ⟨a.val, hTS d a.property⟩

/-- Prescribing complete actual tracks through a finite processed range. -/
def PreservesFiniteTracks (hTS : ∀ d, T d ⊆ S d)
    (R : PartialSimplexStraightening 1 z T F hT N) {r : ℕ}
    (P : PartialSimplexStraightening 1 z S F hS r) : Prop :=
  ∀ d, d < r → ∀ a : {a // a ∈ T d}, P.track d (finiteFamilyInclusion hTS d a) = R.track d a

/-- The native zero simplex is its sole vertex. -/
theorem eq_vertex_zero (a : StdSimplex ℝ (Fin 1)) : a = single 0 :=
  Subsingleton.elim _ _

variable [PathConnectedSpace Z]

/-- The zero-dimensional step keeps prescribed vertex paths and chooses paths only elsewhere. -/
theorem exists_prescribed_vertex_first
    (hTS : ∀ d, T d ⊆ S d) (hFT : ∀ d, F d ⊆ T d)
    (R : PartialSimplexStraightening 1 z T F hT N) (hN : 0 < N) :
    ∃ P : PartialSimplexStraightening 1 z S F hS 1, PreservesFiniteTracks hTS R P := by
  classical
  let P₀ := PartialSimplexStraightening.initial 1 z S F hS
  let L (s : {s // s ∈ S 0}) : C(StdSimplex ℝ (Fin 1) × I, Z) :=
    if ht : s.val ∈ T 0 then R.track 0 ⟨s.val, ht⟩ else
      ⟨fun q ↦ (PathConnectedSpace.somePath (s.val (single 0)) z) q.2,
        by fun_prop⟩
  have hbottom (s : {s // s ∈ S 0}) (a : StdSimplex ℝ (Fin 1)) : L s (a, 0) = s.val a := by
    dsimp only [L]
    split_ifs with ht
    · exact R.bottom 0 _ a
    · exact (PathConnectedSpace.somePath (s.val (single 0)) z).source.trans
        (congrArg s.val (eq_vertex_zero a).symm)
  have htop (s : {s // s ∈ S 0}) (a : StdSimplex ℝ (Fin 1)) : L s (a, 1) = z := by
    dsimp only [L]
    split_ifs with ht
    · exact R.top 0 hN (by omega) _ a
    · exact (PathConnectedSpace.somePath (s.val (single 0)) z).target
  have hstationary (s : {s // s ∈ S 0}) (hs : s.val ∈ F 0) (a) (t) :
      L s (a, t) = s.val a := by
    dsimp only [L]
    rw [dite_eq_left (hFT 0 hs)]
    exact R.stationary 0 _ hs a t
  let P : PartialSimplexStraightening 1 z S F hS 1 := {
    track := Function.update P₀.track 0 L
    bottom := by
      intro d s a
      by_cases hd : d = 0
      · subst d; exact hbottom s a
      · simpa only [Function.update_of_ne hd] using P₀.bottom d s a
    stationary := by
      intro d s hs a t
      by_cases hd : d = 0
      · subst d; exact hstationary s hs a t
      · simpa only [Function.update_of_ne hd] using P₀.stationary d s hs a t
    face := by intro d hd; omega
    top := by
      intro d hd _ s a
      have he : d = 0 := by omega
      subst d
      exact htop s a }
  refine ⟨P, ?_⟩
  intro d hd a
  have he : d = 0 := by omega
  subst d
  change L (finiteFamilyInclusion hTS 0 a) = R.track 0 a
  dsimp only [L, finiteFamilyInclusion]
  rw [dite_eq_left a.property]

omit [PathConnectedSpace Z] in
/-- One positive-dimensional HEP step extends all prescribed tracks literally. -/
theorem exists_prescribed_vertex_succ
    (hTS : ∀ d, T d ⊆ S d) (hFT : ∀ d, F d ⊆ T d)
    (R : PartialSimplexStraightening 1 z T F hT N)
    (d : ℕ) (hdN : d + 1 < N)
    (P : PartialSimplexStraightening 1 z S F hS (d + 1))
    (hP : PreservesFiniteTracks hTS R P) :
    ∃ Q : PartialSimplexStraightening 1 z S F hS (d + 2),
      PreservesFiniteTracks hTS R Q := by
  classical
  choose H hH using P.exists_boundary d
  have hzero (s : {s // s ∈ S (d + 1)}) (a : boundary (d + 1)) :
      H s (a, 0) = s.val a.val := by
    obtain ⟨⟨i, b, t⟩, ht⟩ := simplexFaceCylinderCover_surjective d (a, (0 : I))
    have ha : simplexBoundaryFace d i b = a := congrArg Prod.fst ht
    rw [← ha, hH, P.bottom]
    rfl
  have hprescribed (s : {s // s ∈ S (d + 1)}) (hs : s.val ∈ T (d + 1))
      (a : boundary (d + 1)) (t : I) :
      R.track (d + 1) ⟨s.val, hs⟩ (a.val, t) = H s (a, t) := by
    obtain ⟨⟨i, b, v⟩, hv⟩ := simplexFaceCylinderCover_surjective d (a, t)
    have ha : simplexBoundaryFace d i b = a := congrArg Prod.fst hv
    rw [← ha, hH]
    change R.track (d + 1) ⟨s.val, hs⟩ (map i.succAbove b, t) = _
    rw [R.face d hdN]
    exact (congrArg (fun K ↦ K (b, t)) (hP d (by omega) (hT.face ⟨s.val, hs⟩ i))).symm
  have hex (s : {s // s ∈ S (d + 1)}) :
      ∃ g : C(StdSimplex ℝ (Fin (d + 2)), Z), ∃ K : s.val.Homotopy g,
        (∀ a : boundary (d + 1), ∀ t : I, K (t, a.val) = H s (a, t)) ∧
        (∀ hs : s.val ∈ T (d + 1), ∀ a t, K (t, a) = R.track (d + 1) ⟨s.val, hs⟩ (a, t)) ∧
        (∀ hs : s.val ∈ F (d + 1), ∀ a t, K (t, a) = s.val a) := by
    by_cases hs : s.val ∈ T (d + 1)
    · refine ⟨R.endpoint (d + 1) ⟨s.val, hs⟩, R.homotopy (d + 1) ⟨s.val, hs⟩,
        ?_, ?_, ?_⟩
      · exact hprescribed s hs
      · intros; rfl
      · intro hF a t; exact R.stationary _ _ hF a t
    · obtain ⟨g, K, hK⟩ := exists_simplex_homotopy_extension (d + 1) s.val (H s) (hzero s)
      exact ⟨g, K, hK, fun h ↦ (hs h).elim, fun h ↦ (hs (hFT _ h)).elim⟩
  choose g K hside hkeep hfixed using hex
  let L : {s // s ∈ S (d + 1)} → C(StdSimplex ℝ (Fin (d + 2)) × I, Z) :=
    fun s ↦ ⟨fun q ↦ K s (q.2, q.1), by fun_prop⟩
  let Q : PartialSimplexStraightening 1 z S F hS (d + 2) := {
    track := Function.update P.track (d + 1) L
    bottom := by
      intro e s a
      by_cases he : e = d + 1
      · subst e
        simp only [Function.update_self]
        exact (K s).apply_zero a
      · simpa only [Function.update_of_ne he] using P.bottom e s a
    stationary := by
      intro e s hs a t
      by_cases he : e = d + 1
      · subst e
        simp only [Function.update_self]
        exact hfixed s hs a t
      · simpa only [Function.update_of_ne he] using P.stationary e s hs a t
    face := by
      intro e he s i a t
      by_cases hed : e = d
      · subst e
        simp only [Function.update_self, Function.update_of_ne (Nat.ne_add_one d)]
        exact (hside s (simplexBoundaryFace d i a) t).trans (hH s i a t)
      · have hn : e + 1 ≠ d + 1 := by omega
        have hn' : e ≠ d + 1 := by omega
        simp only [Function.update_of_ne hn, Function.update_of_ne hn']
        exact P.face e (by omega) s i a t
    top := by
      intro e he hn s a
      have he' : e ≠ d + 1 := by omega
      simpa only [Function.update_of_ne he'] using P.top e (by omega) hn s a }
  refine ⟨Q, ?_⟩
  intro e he a
  by_cases heq : e = d + 1
  · subst e
    change Function.update P.track (d + 1) L (d + 1) (finiteFamilyInclusion hTS _ a) = _
    rw [Function.update_self]
    apply ContinuousMap.ext
    intro q
    exact hkeep (finiteFamilyInclusion hTS _ a) a.property q.1 q.2
  · change (Function.update P.track (d + 1) L) e (finiteFamilyInclusion hTS e a) = _
    rw [Function.update_of_ne heq]
    exact hP e (by omega) a

/-- Every actual prescribed finite vertex straightening extends to the larger finite family. -/
theorem exists_prescribed_finite_vertex_straightening
    (hTS : ∀ d, T d ⊆ S d) (hFT : ∀ d, F d ⊆ T d)
    (R : PartialSimplexStraightening 1 z T F hT N) :
    ∃ P : PartialSimplexStraightening 1 z S F hS N, PreservesFiniteTracks hTS R P := by
  have hex (r : ℕ) (hr : r ≤ N) :
      ∃ P : PartialSimplexStraightening 1 z S F hS r, PreservesFiniteTracks hTS R P := by
    induction r with
    | zero => exact ⟨PartialSimplexStraightening.initial 1 z S F hS, by intro d hd; omega⟩
    | succ r ih =>
      cases r with
      | zero => exact exists_prescribed_vertex_first hTS hFT R (by omega)
      | succ d =>
        obtain ⟨P, hP⟩ := ih (by omega)
        exact exists_prescribed_vertex_succ hTS hFT R d (by omega) P hP
  exact hex N le_rfl

end Convexity.StdSimplex
