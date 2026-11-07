/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Analysis.Convex.StdSimplex.FaceCharts
public import Colib.Topology.Realization.Simplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-!
# Realization of a simplicial boundary in actual barycentric coordinates

The comparison is the realized boundary inclusion followed by the existing
native standard-simplex realization homeomorphism. Its finite face charts cover and
glue along their actual common faces. No HEP or realization-product theorem is used.

## Implementation provenance

The 22 declarations from `realizationBoundaryFace` through
`realizationBoundary_locallyCompactSpace` in Quillen
`CategoryTheory/TheoremA/EnrichedBoundaryHEP.lean`, commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, are retained. The finite-simplex
homeomorphism and naturality calls use SimplexCategory.toTopHomeo directly.
Source maps, empty cases, dimension and universes remain.
-/
@[expose] public noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SSet

/-- The realized face inclusion in a simplicial boundary. -/
def realizationBoundaryFace {n : ℕ} (i : Fin (n + 2)) :
    |(Δ[n] : SSet.{u})| ⟶ |(∂Δ[n + 1] : SSet.{u})| :=
  SSet.toTop.map (SSet.boundary.ι i)

/-- Realizing the boundary inclusion and taking barycentric coordinates. -/
def realizationBoundaryCoordinates (n : ℕ) :
    C(|(∂Δ[n] : SSet.{u})|, _root_.stdSimplex ℝ (Fin (n + 1))) :=
  ⟨fun x ↦ SimplexCategory.toTopHomeo ⦋n⦌ (SSet.toTop.map ∂Δ[n].ι x), by fun_prop⟩

@[simp] theorem realizationBoundaryCoordinates_face {n : ℕ} (i : Fin (n + 2))
    (t : |(Δ[n] : SSet.{u})|) :
    realizationBoundaryCoordinates (n + 1) (realizationBoundaryFace i t) =
      stdSimplex.map i.succAbove (SimplexCategory.toTopHomeo ⦋n⦌ t) := by
  change SimplexCategory.toTopHomeo ⦋n + 1⦌
    ((SSet.toTop.map (SSet.boundary.ι i) ≫ SSet.toTop.map ∂Δ[n + 1].ι) t) = _
  rw [← Functor.map_comp, SSet.boundary.ι_ι]
  exact SimplexCategory.toTopHomeo_naturality_apply (SimplexCategory.δ i) t

/-- Every boundary simplex factors through one of its finitely many faces. -/
theorem boundary_simplex_factors {n : ℕ} {m : SimplexCategoryᵒᵖ}
    (s : (∂Δ[n + 1] : SSet.{u}).obj m) :
    ∃ (i : Fin (n + 2)) (f : m.unop ⟶ ⦋n⦌),
      (SSet.boundary.ι i).app m (SSet.stdSimplex.objEquiv.symm f) = s := by
  obtain ⟨i, f, hf⟩ := SimplexCategory.eq_comp_δ_of_not_surjective
    (SSet.stdSimplex.objEquiv s.1) s.2
  refine ⟨i, f, ?_⟩
  apply Subtype.ext
  apply SSet.stdSimplex.objEquiv.injective
  exact hf.symm

/-- The finitely many face charts cover the realized boundary. -/
theorem realizationBoundaryFace_jointly_surjective {n : ℕ}
    (x : |(∂Δ[n + 1] : SSet.{u})|) :
    ∃ (i : Fin (n + 2)) (t : |(Δ[n] : SSet.{u})|), realizationBoundaryFace i t = x := by
  obtain ⟨m, f, t, rfl⟩ := realization_exists_simplex x
  obtain ⟨i, g, hg⟩ := boundary_simplex_factors (SSet.yonedaEquiv f)
  refine ⟨i, SSet.toTop.map (SSet.stdSimplex.map g) t, ?_⟩
  change (SSet.toTop.map (SSet.stdSimplex.map g) ≫
    SSet.toTop.map (SSet.boundary.ι i)) t = _
  rw [← Functor.map_comp]
  have heq : SSet.stdSimplex.map g ≫ SSet.boundary.ι i = f := by
    apply SSet.yonedaEquiv.injective
    simpa only [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_map] using hg
  rw [heq]

instance realizationBoundarySucc_compactSpace (n : ℕ) :
    CompactSpace |(∂Δ[n + 1] : SSet.{u})| := by
  let f : (Σ _ : Fin (n + 2), |(Δ[n] : SSet.{u})|) →
      |(∂Δ[n + 1] : SSet.{u})| := fun z ↦ realizationBoundaryFace z.1 z.2
  have hf : Continuous f := continuous_sigma (fun _ ↦ (realizationBoundaryFace _).hom.continuous)
  exact Function.Surjective.compactSpace hf (fun x ↦ by
    obtain ⟨i, t, ht⟩ := realizationBoundaryFace_jointly_surjective x
    exact ⟨⟨i, t⟩, ht⟩)

instance realizationBoundaryZero_isEmpty : IsEmpty |(∂Δ[0] : SSet.{u})| := ⟨by
  intro x
  obtain ⟨m, f, t, ht⟩ := realization_exists_simplex x
  have h := (SSet.yonedaEquiv f).2
  simp at h⟩

instance realizationBoundary_compactSpace (n : ℕ) :
    CompactSpace |(∂Δ[n] : SSet.{u})| := by
  cases n with
  | zero => infer_instance
  | succ n => infer_instance

instance simplexBoundaryZero_isEmpty : IsEmpty (stdSimplex.boundary 0) :=
  stdSimplex.isEmpty_boundary_zero

/-- Boundary coordinates land in the actual zero-coordinate boundary. -/
theorem realizationBoundaryCoordinates_mem (n : ℕ) (x : |(∂Δ[n] : SSet.{u})|) :
    realizationBoundaryCoordinates n x ∈ stdSimplex.boundary n := by
  cases n with
  | zero => exact isEmptyElim x
  | succ n =>
    obtain ⟨i, t, rfl⟩ := realizationBoundaryFace_jointly_surjective x
    refine ⟨i, ?_⟩
    rw [realizationBoundaryCoordinates_face]
    exact stdSimplex.map_succAbove_self i _

/-- The canonical continuous boundary comparison. -/
def realizationBoundaryComparison (n : ℕ) :
    C(|(∂Δ[n] : SSet.{u})|, stdSimplex.boundary n) :=
  ⟨fun x ↦ ⟨realizationBoundaryCoordinates n x, realizationBoundaryCoordinates_mem n x⟩,
    (realizationBoundaryCoordinates n).continuous.subtype_mk _⟩

/-- Every point on the geometric boundary lies in a realized face. -/
theorem realizationBoundaryComparison_surjective (n : ℕ) :
    Function.Surjective (realizationBoundaryComparison.{u} n) := by
  cases n with
  | zero => exact fun x ↦ isEmptyElim x
  | succ n =>
    rintro ⟨z, i, hi⟩
    obtain ⟨w, hw⟩ := (stdSimplex.mem_range_map_succAbove_iff i z).mpr hi
    refine ⟨realizationBoundaryFace i ((SimplexCategory.toTopHomeo ⦋n⦌).symm w), ?_⟩
    apply Subtype.ext
    change realizationBoundaryCoordinates (n + 1) _ = z
    rw [realizationBoundaryCoordinates_face, Homeomorph.apply_symm_apply, hw]

/-- The two orders of passing to a codimension-two face agree. -/
lemma boundaryFace_pair_relation {n : ℕ} (i j : Fin (n + 3)) (h : i < j) :
    SSet.stdSimplex.δ (j.pred (Fin.ne_zero_of_lt h)) ≫ SSet.boundary.ι i =
      SSet.stdSimplex.δ (i.castPred (Fin.ne_last_of_lt h)) ≫ SSet.boundary.ι j := by
  rw [← cancel_mono ∂Δ[n + 2].ι]
  simp only [Category.assoc, SSet.boundary.ι_ι]
  exact (SSet.stdSimplex.facePairComplIso_hom_ι' i j h).symm.trans
    (SSet.stdSimplex.facePairComplIso_hom_ι i j h)

lemma simplex_face_pair_relation {n : ℕ} (i j : Fin (n + 3)) (h : i < j) :
    SimplexCategory.δ (j.pred (Fin.ne_zero_of_lt h)) ≫ SimplexCategory.δ i =
      SimplexCategory.δ (i.castPred (Fin.ne_last_of_lt h)) ≫ SimplexCategory.δ j := by
  obtain ⟨i, rfl⟩ := i.eq_castSucc_of_ne_last (Fin.ne_last_of_lt h)
  obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero (Fin.ne_zero_of_lt h)
  dsimp
  rw [Fin.pred_succ]
  exact (SimplexCategory.δ_comp_δ (by grind)).symm


/-- Two geometric faces meet along their common codimension-two face. -/
lemma stdSimplex_exists_pair_face {n : ℕ} (i j : Fin (n + 3)) (h : i < j)
    (z : _root_.stdSimplex ℝ (Fin (n + 3))) (hi : z i = 0) (hj : z j = 0) :
    ∃ w : _root_.stdSimplex ℝ (Fin (n + 1)),
      stdSimplex.map i.succAbove
        (stdSimplex.map (j.pred (Fin.ne_zero_of_lt h)).succAbove w) = z ∧
      stdSimplex.map j.succAbove
        (stdSimplex.map (i.castPred (Fin.ne_last_of_lt h)).succAbove w) = z := by
  obtain ⟨v, hv⟩ := (stdSimplex.mem_range_map_succAbove_iff i z).mpr hi
  have hvj : v (j.pred (Fin.ne_zero_of_lt h)) = 0 := by
    rw [← stdSimplex.map_apply_injective Fin.succAbove_right_injective v
      (j.pred (Fin.ne_zero_of_lt h)), Fin.succAbove_pred_of_lt i j h, hv]
    exact hj
  obtain ⟨w, hw⟩ := (stdSimplex.mem_range_map_succAbove_iff
    (j.pred (Fin.ne_zero_of_lt h)) v).mpr hvj
  have hwi := (congrArg (stdSimplex.map i.succAbove) hw).trans hv
  refine ⟨w, hwi, ?_⟩
  have he : i.succAbove ∘ (j.pred (Fin.ne_zero_of_lt h)).succAbove =
      j.succAbove ∘ (i.castPred (Fin.ne_last_of_lt h)).succAbove := by
    funext k
    exact ConcreteCategory.congr_hom (simplex_face_pair_relation i j h) k
  simpa only [stdSimplex.map_comp_apply, he] using hwi

/-- Distinct realized face charts agree whenever their barycentric points agree. -/
lemma realizationBoundaryFace_overlap_ordered {n : ℕ} (i j : Fin (n + 3)) (h : i < j)
    (v w : _root_.stdSimplex ℝ (Fin (n + 2)))
    (hvw : stdSimplex.map i.succAbove v = stdSimplex.map j.succAbove w) :
    realizationBoundaryFace.{u} i ((SimplexCategory.toTopHomeo ⦋n + 1⦌).symm v) =
      realizationBoundaryFace j ((SimplexCategory.toTopHomeo ⦋n + 1⦌).symm w) := by
  have hi : (stdSimplex.map i.succAbove v) i = 0 :=
    stdSimplex.map_succAbove_self i v
  have hj : (stdSimplex.map i.succAbove v) j = 0 := by
    rw [hvw]
    exact stdSimplex.map_succAbove_self j w
  obtain ⟨z, hzi, hzj⟩ := stdSimplex_exists_pair_face i j h _ hi hj
  have hv : stdSimplex.map (j.pred (Fin.ne_zero_of_lt h)).succAbove z = v :=
    stdSimplex.simplex_map_injective (Fin.succAbove_right_injective (p := i)) hzi
  have hw : stdSimplex.map (i.castPred (Fin.ne_last_of_lt h)).succAbove z = w :=
    stdSimplex.simplex_map_injective (Fin.succAbove_right_injective (p := j)) (hzj.trans hvw)
  rw [← hv, ← hw]
  change realizationBoundaryFace i ((SimplexCategory.toTopHomeo ⦋n + 1⦌).symm
      (stdSimplex.map (SimplexCategory.δ (j.pred (Fin.ne_zero_of_lt h))) z)) =
    realizationBoundaryFace j ((SimplexCategory.toTopHomeo ⦋n + 1⦌).symm
      (stdSimplex.map (SimplexCategory.δ (i.castPred (Fin.ne_last_of_lt h))) z))
  rw [SimplexCategory.toTopHomeo_symm_naturality_apply,
    SimplexCategory.toTopHomeo_symm_naturality_apply]
  change (SSet.toTop.map (SSet.stdSimplex.δ _) ≫ SSet.toTop.map (SSet.boundary.ι i)) _ =
    (SSet.toTop.map (SSet.stdSimplex.δ _) ≫ SSet.toTop.map (SSet.boundary.ι j)) _
  rw [← Functor.map_comp, ← Functor.map_comp, boundaryFace_pair_relation i j h]

/-- All realized boundary charts identify exactly their common geometric faces. -/
lemma realizationBoundaryFace_overlap {n : ℕ} (i j : Fin (n + 2))
    (v w : _root_.stdSimplex ℝ (Fin (n + 1)))
    (hvw : stdSimplex.map i.succAbove v = stdSimplex.map j.succAbove w) :
    realizationBoundaryFace.{u} i ((SimplexCategory.toTopHomeo ⦋n⦌).symm v) =
      realizationBoundaryFace j ((SimplexCategory.toTopHomeo ⦋n⦌).symm w) := by
  by_cases hij : i = j
  · subst j
    have hvw' := stdSimplex.simplex_map_injective (Fin.succAbove_right_injective (p := i)) hvw
    rw [hvw']
  cases n with
  | zero =>
    have hv : v = stdSimplex.vertex (0 : Fin 1) := Subsingleton.elim _ _
    have hw : w = stdSimplex.vertex (0 : Fin 1) := Subsingleton.elim _ _
    rw [hv, hw, stdSimplex.map_vertex, stdSimplex.map_vertex] at hvw
    have he := stdSimplex.vertex_injective hvw
    fin_cases i <;> fin_cases j <;> simp_all
  | succ n =>
    rcases lt_or_gt_of_ne hij with h | h
    · exact realizationBoundaryFace_overlap_ordered i j h v w hvw
    · exact (realizationBoundaryFace_overlap_ordered j i h w v hvw.symm).symm

/-- The boundary comparison is injective, including all face intersections. -/
theorem realizationBoundaryComparison_injective (n : ℕ) :
    Function.Injective (realizationBoundaryComparison.{u} n) := by
  intro x y h
  cases n with
  | zero => exact isEmptyElim x
  | succ n =>
    obtain ⟨i, s, rfl⟩ := realizationBoundaryFace_jointly_surjective x
    obtain ⟨j, t, rfl⟩ := realizationBoundaryFace_jointly_surjective y
    obtain ⟨v, rfl⟩ := (SimplexCategory.toTopHomeo ⦋n⦌).symm.surjective s
    obtain ⟨w, rfl⟩ := (SimplexCategory.toTopHomeo ⦋n⦌).symm.surjective t
    have h' := congrArg Subtype.val h
    change realizationBoundaryCoordinates (n + 1) _ =
      realizationBoundaryCoordinates (n + 1) _ at h'
    simp only [realizationBoundaryCoordinates_face, Homeomorph.apply_symm_apply] at h'
    exact realizationBoundaryFace_overlap i j v w h'

/-- Realization of the simplicial boundary is its actual barycentric boundary. -/
def realizationBoundaryHomeomorph (n : ℕ) :
    |(∂Δ[n] : SSet.{u})| ≃ₜ stdSimplex.boundary n :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (realizationBoundaryComparison n)
      ⟨realizationBoundaryComparison_injective n, realizationBoundaryComparison_surjective n⟩)
    (realizationBoundaryComparison n).continuous

instance realizationBoundary_t2Space (n : ℕ) : T2Space |(∂Δ[n] : SSet.{u})| :=
  (realizationBoundaryHomeomorph n).symm.t2Space

instance realizationBoundary_locallyCompactSpace (n : ℕ) :
    LocallyCompactSpace |(∂Δ[n] : SSet.{u})| := inferInstance

end SSet
