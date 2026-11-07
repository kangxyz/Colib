/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.PrescribedFiniteVertexStraightening

/-!
# Finite vertex straightening through an actual injective map

The source straightening fixes every already-based simplex. Actual injectivity
makes each image simplex have one source preimage, and reflects a based image
simplex to a based source simplex. Thus the source tracks descend to a genuine
face-compatible image-family straightening, stationary on every based target
simplex in that family.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u

namespace stdSimplex
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The original based-vertex condition, before any homotopy replacement. -/
def SimplexVerticesAt {d : ℕ} (x : X) (a : C(_root_.stdSimplex ℝ (Fin (d + 1)), X)) : Prop :=
  ∀ i, a (stdSimplex.vertex i) = x

/-- Every original face of a based simplex is based at the same original point. -/
theorem SimplexVerticesAt.face {d : ℕ} {x : X}
    {a : C(_root_.stdSimplex ℝ (Fin (d + 2)), X)} (ha : SimplexVerticesAt x a) (i : Fin (d + 2)) :
    SimplexVerticesAt x (singularVertexRestriction a i.succAbove) := by
  intro j
  change a (stdSimplex.map i.succAbove (stdSimplex.vertex j)) = x
  rw [stdSimplex.map_vertex]
  exact ha _

/-- A zero-simplex with its original vertex at x is literally the constant map. -/
theorem SimplexVerticesAt.zero {x : X} {a : C(_root_.stdSimplex ℝ (Fin 1), X)}
    (ha : SimplexVerticesAt x a) : a = ContinuousMap.const _ x := by
  ext t
  exact (congrArg a (eq_vertex_zero t)).trans (ha 0)

/-- Select every already-based simplex in a finite actual family. -/
def basedFiniteFamily (x : X) (S : FiniteSimplexFamily X) : FiniteSimplexFamily X := by
  classical
  exact fun d ↦ (S d).filter (SimplexVerticesAt x)

/-- The selected original based simplices form a face-closed family. -/
theorem basedFiniteFamily_faceClosed (x : X) {S : FiniteSimplexFamily X} (hS : S.FaceClosed) :
    (basedFiniteFamily x S).FaceClosed := by
  classical
  intro d a ha i
  obtain ⟨has, hab⟩ := Finset.mem_filter.mp ha
  exact Finset.mem_filter.mpr ⟨hS d a has i, hab.face i⟩

/-- The actual source vertex straightening fixes all originally based source simplices. -/
theorem exists_based_finite_vertex_straightening [PathConnectedSpace X]
    (x : X) (S : FiniteSimplexFamily X) (hS : S.FaceClosed) (N : ℕ) :
    Nonempty (PartialSimplexStraightening 1 x S (basedFiniteFamily x S) hS N) := by
  classical
  let F := basedFiniteFamily x S
  let hF : F.FaceClosed := basedFiniteFamily_faceClosed x hS
  let R : PartialSimplexStraightening 1 x F F hF N := {
    track d a := ⟨fun q ↦ a.val q.1, by fun_prop⟩
    bottom _ _ _ := rfl
    stationary _ _ _ _ _ := rfl
    face _ _ _ _ _ _ := rfl
    top := by
      intro d _ hd a t
      have he : d = 0 := by omega
      subst d
      exact ContinuousMap.congr_fun (Finset.mem_filter.mp a.property).2.zero t }
  obtain ⟨P, _⟩ := exists_prescribed_finite_vertex_straightening
    (S := S) (hS := hS) (T := F) (hT := hF)
    (fun d ↦ Finset.filter_subset _ _) (fun _ ↦ Set.Subset.rfl) R
  exact ⟨P⟩

/-- The degreewise image consists of actual postcomposed source simplex maps. -/
def imageFiniteFamily (j : C(X, Y)) (S : FiniteSimplexFamily X) : FiniteSimplexFamily Y := by
  classical
  exact fun d ↦ (S d).image (j.comp ·)

/-- Postcomposition commutes literally with every original face restriction. -/
theorem comp_singularVertexRestriction (j : C(X, Y)) {d e : ℕ}
    (a : C(_root_.stdSimplex ℝ (Fin (e + 1)), X)) (α : Fin (d + 1) → Fin (e + 1)) :
    j.comp (singularVertexRestriction a α) = singularVertexRestriction (j.comp a) α := rfl

/-- The actual finite image is face closed. -/
theorem imageFiniteFamily_faceClosed (j : C(X, Y))
    {S : FiniteSimplexFamily X} (hS : S.FaceClosed) : (imageFiniteFamily j S).FaceClosed := by
  classical
  intro d a ha i
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  exact Finset.mem_image.mpr ⟨singularVertexRestriction b i.succAbove, hS d b hb i, rfl⟩

/-- Injectivity identifies equal source simplex maps from their original images. -/
theorem comp_simplex_injective (j : C(X, Y)) (hj : Function.Injective j) (d : ℕ) :
    Function.Injective (j.comp · : C(_root_.stdSimplex ℝ (Fin (d + 1)), X) → _) := by
  intro a b hab
  ext t
  exact hj (ContinuousMap.congr_fun hab t)

/-- The unique actual source index for an original image-family simplex. -/
def imageFiniteFamilyPreimage (j : C(X, Y)) (S : FiniteSimplexFamily X) (d : ℕ)
    (a : {a // a ∈ imageFiniteFamily j S d}) : {b // b ∈ S d} := by
  classical
  exact ⟨Classical.choose (Finset.mem_image.mp a.property),
    (Classical.choose_spec (Finset.mem_image.mp a.property)).1⟩

/-- The chosen index maps to exactly the original image simplex, without reparametrization. -/
theorem imageFiniteFamilyPreimage_comp (j : C(X, Y)) (S : FiniteSimplexFamily X) (d : ℕ)
    (a : {a // a ∈ imageFiniteFamily j S d}) :
    j.comp (imageFiniteFamilyPreimage j S d a).val = a.val := by
  classical
  exact (Classical.choose_spec (Finset.mem_image.mp a.property)).2

/-- Equal image faces give the same source face index, by actual injectivity. -/
theorem imageFiniteFamilyPreimage_face (j : C(X, Y)) (hj : Function.Injective j)
    {S : FiniteSimplexFamily X} (hS : S.FaceClosed) {d : ℕ}
    (a : {a // a ∈ imageFiniteFamily j S (d + 1)}) (i : Fin (d + 2)) :
    imageFiniteFamilyPreimage j S d ((imageFiniteFamily_faceClosed j hS).face a i) =
      hS.face (imageFiniteFamilyPreimage j S (d + 1) a) i := by
  apply Subtype.ext
  apply comp_simplex_injective j hj d
  change j.comp (imageFiniteFamilyPreimage j S d
      ((imageFiniteFamily_faceClosed j hS).face a i)).val =
    j.comp (hS.face (imageFiniteFamilyPreimage j S (d + 1) a) i).val
  rw [imageFiniteFamilyPreimage_comp]
  change singularVertexRestriction a.val i.succAbove =
    j.comp (singularVertexRestriction (imageFiniteFamilyPreimage j S (d + 1) a).val i.succAbove)
  rw [comp_singularVertexRestriction, imageFiniteFamilyPreimage_comp]

/-- The original source straightening descends to its actual finite image family. -/
def imageFiniteVertexStraightening (j : C(X, Y)) (hj : Function.Injective j)
    (x : X) {S : FiniteSimplexFamily X} (hS : S.FaceClosed) {N : ℕ}
    (R : PartialSimplexStraightening 1 x S (basedFiniteFamily x S) hS N)
    (F : FiniteSimplexFamily Y) (hF : ∀ d a, a ∈ F d → SimplexVerticesAt (j x) a) :
    PartialSimplexStraightening 1 (j x) (imageFiniteFamily j S) F
      (imageFiniteFamily_faceClosed j hS) N where
  track d a := j.comp (R.track d (imageFiniteFamilyPreimage j S d a))
  bottom d a t := by
    change j (R.track d (imageFiniteFamilyPreimage j S d a) (t, 0)) = a.val t
    rw [R.bottom]
    exact ContinuousMap.congr_fun (imageFiniteFamilyPreimage_comp j S d a) t
  stationary d a ha t s := by
    classical
    have hbased : SimplexVerticesAt x (imageFiniteFamilyPreimage j S d a).val := by
      intro i
      apply hj
      exact (ContinuousMap.congr_fun (imageFiniteFamilyPreimage_comp j S d a)
        (stdSimplex.vertex i)).trans (hF d a.val ha i)
    have hs : (imageFiniteFamilyPreimage j S d a).val ∈ basedFiniteFamily x S d :=
      Finset.mem_filter.mpr ⟨(imageFiniteFamilyPreimage j S d a).property, hbased⟩
    change j (R.track d (imageFiniteFamilyPreimage j S d a) (t, s)) = _
    rw [R.stationary d _ hs]
    exact ContinuousMap.congr_fun (imageFiniteFamilyPreimage_comp j S d a) t
  face d hd a i t s := by
    change j (R.track (d + 1) (imageFiniteFamilyPreimage j S (d + 1) a)
      (stdSimplex.map i.succAbove t, s)) = _
    rw [R.face d hd]
    exact congrArg (fun b ↦ j (R.track d b (t, s)))
      (imageFiniteFamilyPreimage_face j hj hS a i).symm
  top d hd hn a t := by
    change j (R.track d (imageFiniteFamilyPreimage j S d a) (t, 1)) = _
    rw [R.top d hd hn]

end stdSimplex
