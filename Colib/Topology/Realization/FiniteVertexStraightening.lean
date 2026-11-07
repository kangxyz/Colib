/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, OpenAI
-/
module
public import Colib.Topology.ContinuousMap
public import Colib.Topology.Realization.FiniteSimplexFamily
public import Colib.Topology.Realization.SimplexFaceGluing
public import Colib.Analysis.Convex.StdSimplex.BoundaryHomotopyExtension
/-! # Actual finite vertex tracks

Adapted at cutoff one from Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Positive-dimensional extension
uses the explicit native boundary retraction, not higher connectivity.
-/
@[expose] public noncomputable section
open scoped Topology unitInterval
universe u
namespace Convexity.StdSimplex
variable {Z : Type u} [TopologicalSpace Z]
theorem exists_simplex_homotopy_extension (d : ℕ)
    (f : C(StdSimplex ℝ (Fin (d + 1)), Z))
    (H : C(boundary d × I, Z))
    (hzero : ∀ b : boundary d, H (b, 0) = f b.val) :
    ∃ g : C(StdSimplex ℝ (Fin (d + 1)), Z), ∃ K : f.Homotopy g,
      ∀ (b : boundary d) (t : I), K (t, b.val) = H (b, t) := by
  let f' : C(Unit × StdSimplex ℝ (Fin (d + 1)), Z) :=
    ⟨fun x ↦ f x.2, by fun_prop⟩
  let H' : C((Unit × boundary d) × I, Z) :=
    ⟨fun x ↦ H (x.1.2, x.2), by fun_prop⟩
  have hzero' : ∀ x b, H' ((x, b), 0) = f' (x, b.val) := fun _ b ↦ hzero b
  let L := simplexBoundaryHomotopyExtension d f' H' hzero'
  let g : C(StdSimplex ℝ (Fin (d + 1)), Z) := ⟨fun x ↦ L (((), x), 1), by fun_prop⟩
  refine ⟨g, {
    toFun x := L (((), x.2), x.1)
    continuous_toFun := by fun_prop
    map_zero_left x := simplexBoundaryHomotopyExtension_zero d f' H' hzero' () x
    map_one_left _ := rfl }, fun x t ↦ ?_⟩
  exact simplexBoundaryHomotopyExtension_side d f' H' hzero' () x t

/-- Two already coherent adjacent levels give the genuine continuous boundary
track of each next simplex. The double-face equality uses actual simplex
identity, so cancellation is not split into unrelated occurrence choices. -/
theorem exists_simplex_boundary_track_of_family (S : FiniteSimplexFamily Z)
    (hS : S.FaceClosed) (d : ℕ)
    (L : {s // s ∈ S d} → C(StdSimplex ℝ (Fin (d + 1)) × I, Z))
    (K : {s // s ∈ S (d + 1)} → C(StdSimplex ℝ (Fin (d + 2)) × I, Z))
    (hface : ∀ (s : {s // s ∈ S (d + 1)}) (i : Fin (d + 2))
      (x : StdSimplex ℝ (Fin (d + 1))) (t : I),
      K s (map i.succAbove x, t) = L (hS.face s i) (x, t))
    (τ : {τ // τ ∈ S (d + 2)}) :
    ∃ H : C(boundary (d + 2) × I, Z),
      ∀ (i : Fin (d + 3)) (x : StdSimplex ℝ (Fin (d + 2))) (t : I),
        H (simplexBoundaryFace (d + 1) i x, t) = K (hS.face τ i) (x, t) := by
  apply exists_simplex_boundary_track_of_faces d (fun i ↦ K (hS.face τ i))
  intro i k q t
  rw [hface, hface, hS.face_face τ i k]

/-- Arbitrary tracks on the two vertices glue on the genuine interval boundary. -/
theorem exists_simplex_boundary_track_one
    (H : Fin 2 → C(StdSimplex ℝ (Fin 1) × I, Z)) :
    ∃ K : C(boundary 1 × I, Z),
      ∀ (i : Fin 2) (x : StdSimplex ℝ (Fin 1)) (t : I),
        K (simplexBoundaryFace 0 i x, t) = H i (x, t) := by
  apply exists_simplex_boundary_track 0 H
  intro i j x y t h
  by_cases hij : j = i
  · subst j
    have hxy := simplex_map_injective Fin.succAbove_right_injective h
    subst y
    rfl
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hij
    have hz := map_succAbove_self (i.succAbove k) y
    rw [← h, map_apply_injective Fin.succAbove_right_injective] at hz
    have hk : k = 0 := Fin.eq_zero k
    subst k
    have hx : x.weights (0 : Fin 1) = 1 := by simp
    exact (zero_ne_one (hz.symm.trans hx)).elim

/-- The inductive data are actual continuous tracks, not a filler assumption.
Only dimensions strictly below the bound have been straightened. -/
structure PartialSimplexStraightening (n : ℕ) (z : Z)
    (S F : FiniteSimplexFamily Z) (hS : S.FaceClosed) (N : ℕ) where
  /-- The actual shared continuous homotopy track in each degree. -/
  track : ∀ d, {s // s ∈ S d} → C(StdSimplex ℝ (Fin (d + 1)) × I, Z)
  /-- Every track begins at the original singular simplex. -/
  bottom : ∀ d s x, track d s (x, 0) = s.val x
  /-- Selected fixed maps retain every point for every time. -/
  stationary : ∀ d (s : {s // s ∈ S d}), s.val ∈ F d →
    ∀ x t, track d s (x, t) = s.val x
  /-- All already processed face restrictions commute exactly. -/
  face : ∀ d, d + 1 < N → ∀ (s : {s // s ∈ S (d + 1)}) i x t,
    track (d + 1) s (map i.succAbove x, t) = track d (hS.face s i) (x, t)
  /-- Processed dimensions below the cutoff end at the basepoint. -/
  top : ∀ d, d < N → d < n → ∀ s x, track d s (x, 1) = z

namespace PartialSimplexStraightening

variable {n N : ℕ} {z : Z} {S F : FiniteSimplexFamily Z} {hS : S.FaceClosed}

/-- Stationary maps initialize the induction without any topological hypothesis. -/
def initial (n : ℕ) (z : Z) (S F : FiniteSimplexFamily Z) (hS : S.FaceClosed) :
    PartialSimplexStraightening n z S F hS 0 where
  track d s := ⟨fun x ↦ s.val x.1, by fun_prop⟩
  bottom _ _ _ := rfl
  stationary _ _ _ _ _ := rfl
  face _ h := by omega
  top _ h := by omega

/-- The next boundary is assembled from the previously constructed face tracks.
In positive codimension two, overlap follows from the actual double-face law. -/
theorem exists_boundary (d : ℕ)
    (P : PartialSimplexStraightening n z S F hS (d + 1))
    (s : {s // s ∈ S (d + 1)}) :
    ∃ H : C(boundary (d + 1) × I, Z),
      ∀ i x t, H (simplexBoundaryFace d i x, t) = P.track d (hS.face s i) (x, t) := by
  cases d with
  | zero => exact exists_simplex_boundary_track_one (fun i ↦ P.track 0 (hS.face s i))
  | succ d =>
    exact exists_simplex_boundary_track_of_family S hS d (P.track d) (P.track (d + 1))
      (P.face d (by omega)) s

end PartialSimplexStraightening
namespace PartialSimplexStraightening

variable {n N : ℕ} {z : Z} {S F : FiniteSimplexFamily Z} {hS : S.FaceClosed}

/-- The actual endpoint replacement in each dimension. -/
def endpoint (P : PartialSimplexStraightening n z S F hS N) (d : ℕ)
    (s : {s // s ∈ S d}) : C(StdSimplex ℝ (Fin (d + 1)), Z) :=
  ⟨fun x ↦ P.track d s (x, 1), by fun_prop⟩

/-- Every constructed track is an actual homotopy from the original simplex. -/
def homotopy (P : PartialSimplexStraightening n z S F hS N) (d : ℕ)
    (s : {s // s ∈ S d}) : s.val.Homotopy (P.endpoint d s) where
  toFun x := P.track d s (x.2, x.1)
  continuous_toFun := by fun_prop
  map_zero_left := P.bottom d s
  map_one_left _ := rfl

/-- Endpoint replacements commute literally with every standard face below the bound. -/
theorem endpoint_face (P : PartialSimplexStraightening n z S F hS N)
    (d : ℕ) (hd : d + 1 < N) (s : {s // s ∈ S (d + 1)}) (i : Fin (d + 2)) :
    singularVertexRestriction (P.endpoint (d + 1) s) i.succAbove =
      P.endpoint d (hS.face s i) := by
  ext x
  exact P.face d hd s i x 1

/-- Low-dimensional endpoint maps are exactly the constant singular simplex. -/
theorem endpoint_eq_const (P : PartialSimplexStraightening n z S F hS N)
    (d : ℕ) (hd : d < N) (hn : d < n) (s : {s // s ∈ S d}) :
    P.endpoint d s = ContinuousMap.const _ z := by
  ext x
  exact P.top d hd hn s x

/-- Selected original maps retain every point for the whole homotopy. -/
theorem homotopy_stationary (P : PartialSimplexStraightening n z S F hS N)
    (d : ℕ) (s : {s // s ∈ S d}) (hs : s.val ∈ F d) (t : I)
    (x : StdSimplex ℝ (Fin (d + 1))) : P.homotopy d s (t, x) = s.val x :=
  P.stationary d s hs x t

/-- Every processed endpoint has all of its original vertices at the basepoint. -/
theorem endpoint_vertices (P : PartialSimplexStraightening 1 z S F hS N)
    (d : ℕ) (hd : d < N) (s : {s // s ∈ S d}) (v : Fin (d + 1)) :
    P.endpoint d s (single v) = z := by
  induction d with
  | zero => exact P.top 0 hd (by omega) s _
  | succ d ih =>
    obtain ⟨i, hi⟩ := exists_ne v
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq (Ne.symm hi)
    rw [← hk, ← map_single]
    change P.track (d + 1) s (map i.succAbove (single k), 1) = z
    rw [P.face d hd]
    exact ih (by omega) (hS.face s i) k

/-- A selected fixed simplex keeps its exact original endpoint. -/
theorem endpoint_fixed (P : PartialSimplexStraightening n z S F hS N)
    (d : ℕ) (s : {s // s ∈ S d}) (hs : s.val ∈ F d) : P.endpoint d s = s.val := by
  ext x
  exact P.stationary d s hs x 1

end PartialSimplexStraightening

end Convexity.StdSimplex
