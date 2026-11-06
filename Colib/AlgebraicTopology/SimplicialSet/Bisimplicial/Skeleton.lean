/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremA.Coend
public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-! Implementation provenance: adapted from
`Quillen/Topology/Realization/BisimplicialSkeleton.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The native simplicial objects,
realization maps and full proof are retained. -/

/-!
# The outer skeletal filtration of a bisimplicial set

The filtration uses the full coefficient row in each outer degree. Its value
in inner degree `q` is the ordinary skeleton of the outer simplicial set
obtained by evaluating at `q`, evaluated at outer degree `q`.
-/
@[expose] public section


noncomputable section

open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SSet.BisimplicialRealization

open CategoryTheory.TheoremA

variable (X : SimplexCategoryᵒᵖ ⥤ SSet.{u})

/-- The outer simplicial set at a fixed inner degree. -/
abbrev column (q : SimplexCategoryᵒᵖ) : SSet.{u} :=
  X ⋙ (evaluation _ _).obj q

/-- The outer skeleton, indexed so stage `k` contains outer dimensions `< k`. -/
def outerSkeleton : ℕ →o (diagonalSSet X).Subcomplex where
  toFun k := ⨆ (m : Fin k), SSet.Subcomplex.range (diagonalEvaluation X ⦋m.val⦌)
  monotone' k l h := by
    simp only [iSup_le_iff]
    intro m
    exact le_iSup (fun m : Fin l ↦
      SSet.Subcomplex.range (diagonalEvaluation X ⦋m.val⦌)) ⟨m.val, lt_of_lt_of_le m.isLt h⟩

lemma mem_outerSkeleton_iff (k : ℕ) (q : SimplexCategoryᵒᵖ)
    (x : (diagonalSSet X).obj q) :
    x ∈ (outerSkeleton X k).obj q ↔
      ∃ (m : ℕ) (_ : m < k) (f : q.unop ⟶ ⦋m⦌)
        (y : (X.obj (op ⦋m⦌)).obj q), (X.map f.op).app q y = x := by
  simp only [outerSkeleton, OrderHom.coe_mk, Subfunctor.iSup_obj,
    Set.mem_iUnion, Subfunctor.range_obj, Set.mem_range]
  constructor
  · rintro ⟨m, ⟨y, f⟩, h⟩
    exact ⟨m.val, m.isLt, f.down, y, h⟩
  · rintro ⟨m, hm, f, y, h⟩
    exact ⟨⟨m, hm⟩, (y, ULift.up f), h⟩

lemma mem_skeleton_iff_exists (A : SSet.{u}) (k : ℕ)
    (q : SimplexCategoryᵒᵖ) (x : A.obj q) :
    x ∈ (A.skeleton k).obj q ↔
      ∃ (m : ℕ) (_ : m < k) (f : q.unop ⟶ ⦋m⦌)
        (y : A.obj (op ⦋m⦌)), A.map f.op y = x := by
  constructor
  · intro hx
    simp only [SSet.skeleton, OrderHom.coe_mk, Subfunctor.iSup_obj,
      Set.mem_iUnion] at hx
    obtain ⟨m, y, hy⟩ := hx
    obtain ⟨f, hf⟩ := (SSet.Subcomplex.mem_ofSimplex_obj_iff y.val x).1 hy
    exact ⟨m.val, m.isLt, f, y.val, hf⟩
  · rintro ⟨m, hm, f, y, rfl⟩
    exact (A.skeleton k).map f.op (A.mem_skeleton y hm)

/-- Pointwise identification with the ordinary outer skeleton. -/
lemma mem_outerSkeleton_iff_column (k : ℕ) (q : SimplexCategoryᵒᵖ)
    (x : (diagonalSSet X).obj q) :
    x ∈ (outerSkeleton X k).obj q ↔
      x ∈ ((column X q).skeleton k).obj q := by
  rw [mem_outerSkeleton_iff, mem_skeleton_iff_exists]
  rfl

@[simp]
lemma outerSkeleton_zero : outerSkeleton X 0 = ⊥ := by
  ext q x
  simp [mem_outerSkeleton_iff]

lemma outerSkeleton_succ (n : ℕ) :
    outerSkeleton X (n + 1) = outerSkeleton X n ⊔
      SSet.Subcomplex.range (diagonalEvaluation X ⦋n⦌) := by
  ext q x
  simp only [mem_outerSkeleton_iff, Subfunctor.max_obj, Set.mem_union,
    Subfunctor.range_obj, Set.mem_range]
  constructor
  · rintro ⟨m, hm, f, y, h⟩
    obtain hm | rfl := (Nat.lt_succ_iff.mp hm).lt_or_eq
    · exact Or.inl ⟨m, hm, f, y, h⟩
    · exact Or.inr ⟨(y, ULift.up f), h⟩
  · rintro (⟨m, hm, f, y, h⟩ | ⟨⟨y, f⟩, h⟩)
    · exact ⟨m, Nat.lt_succ_of_lt hm, f, y, h⟩
    · exact ⟨n, Nat.lt_succ_self n, f.down, y, h⟩

lemma iSup_outerSkeleton : ⨆ n : ℕ, outerSkeleton X n = ⊤ := by
  apply le_antisymm (by simp)
  intro q x _
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion]
  refine ⟨q.unop.len + 1, (mem_outerSkeleton_iff X _ _ _).2 ?_⟩
  refine ⟨q.unop.len, Nat.lt_succ_self _, 𝟙 _, x, ?_⟩
  simp

/-- The actual simplicial set at a stage of the outer filtration. -/
abbrev stage (n : ℕ) : SSet.{u} := outerSkeleton X n

/-- The increasing outer-skeleton diagram. -/
def stageDiagram : ℕ ⥤ SSet.{u} :=
  (outerSkeleton X).monotone.functor ⋙ SSet.Subcomplex.toSSetFunctor

/-- The inclusions into the diagonal form the filtration cocone. -/
def stageCocone : Cocone (stageDiagram X) where
  pt := diagonalSSet X
  ι.app n := SSet.Subcomplex.ι (outerSkeleton X n)

/-- The diagonal is the genuine sequential colimit of its outer skeletons. -/
def stageCoconeIsColimit : IsColimit (stageCocone X) :=
  IsColimit.ofIsoColimit (isColimitOfPreserves SSet.Subcomplex.toSSetFunctor
    ((CompleteLattice.colimitCocone (outerSkeleton X).monotone.functor).isColimit))
    (Cocone.ext (SSet.Subcomplex.eqToIso (iSup_outerSkeleton X) ≪≫
      SSet.Subcomplex.topIso (diagonalSSet X)))

/-- Maps of bisimplicial sets preserve every outer-skeleton stage. -/
lemma diagonalMap_mem_outerSkeleton {X Y : SimplexCategoryᵒᵖ ⥤ SSet.{u}}
    (η : X ⟶ Y) (k : ℕ) (q : SimplexCategoryᵒᵖ)
    (x : (diagonalSSet X).obj q) (hx : x ∈ (outerSkeleton X k).obj q) :
    (diagonalMap η).app q x ∈ (outerSkeleton Y k).obj q := by
  obtain ⟨m, hm, f, y, rfl⟩ := (mem_outerSkeleton_iff X k q x).1 hx
  refine (mem_outerSkeleton_iff Y k q _).2
    ⟨m, hm, f, (η.app (op ⦋m⦌)).app q y, ?_⟩
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app (η.naturality f.op) q) y).symm

/-- The canonical map on an outer-skeleton stage. -/
def stageMap {X Y : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (η : X ⟶ Y) (k : ℕ) :
    stage X k ⟶ stage Y k where
  app q := ↾fun x ↦ ⟨(diagonalMap η).app q x.val,
    diagonalMap_mem_outerSkeleton η k q x.val x.property⟩
  naturality p q f := by
    ext x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((diagonalMap η).naturality f) x.val

@[reassoc (attr := simp)]
lemma stageMap_ι {X Y : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (η : X ⟶ Y) (k : ℕ) :
    stageMap η k ≫ (outerSkeleton Y k).ι =
      (outerSkeleton X k).ι ≫ diagonalMap η := rfl

/-- The canonical map of the sequential outer-skeleton diagrams. -/
def stageDiagramMap {X Y : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (η : X ⟶ Y) :
    stageDiagram X ⟶ stageDiagram Y where
  app k := stageMap η k
  naturality _ _ _ := rfl

/-- Evaluation lies in the preceding skeleton exactly along the degenerate
coefficient simplices or the boundary of the representing simplex. -/
lemma map_mem_skeleton_iff (A : SSet.{u}) {n : ℕ}
    {q : SimplexCategory} (f : q ⟶ ⦋n⦌) (x : A.obj (op ⦋n⦌)) :
    A.map f.op x ∈ (A.skeleton n).obj (op q) ↔
      x ∈ A.degenerate n ∨ ¬ Epi f := by
  constructor
  · intro hx
    by_cases hf : Epi f
    · apply Or.inl
      by_contra hn
      have hxnd : x ∈ A.nonDegenerate n := hn
      have := hf
      have := isSplitEpi_of_epi f
      have h := (A.skeleton n).map (section_ f).op hx
      change A.map (section_ f).op (A.map f.op x) ∈
        (A.skeleton n).obj (op ⦋n⦌) at h
      have hxsk : x ∈ (A.skeleton n).obj (op ⦋n⦌) := by
        simpa [← Functor.map_comp_apply, ← op_comp] using h
      have hnlt := (A.mem_skeleton_obj_iff_of_nonDegenerate ⟨x, hxnd⟩ n).1 hxsk
      exact (lt_irrefl n) hnlt
    · exact Or.inr hf
  · rintro (⟨m, hm, g, y, rfl⟩ | hf)
    · apply (mem_skeleton_iff_exists A n (op q) _).2
      exact ⟨m, hm, f ≫ g, y, by simp⟩
    · have hi : (image f).len < n := by
        by_contra! hn
        have hle := SimplexCategory.len_le_of_mono (image.ι f)
        have : IsIso (image.ι f) :=
          (SimplexCategory.isIso_iff_of_mono _).2 (Nat.le_antisymm hle hn)
        apply hf
        rw [← image.fac f]
        infer_instance
      apply (mem_skeleton_iff_exists A n (op q) _).2
      refine ⟨(image f).len, hi, factorThruImage f, A.map (image.ι f).op x, ?_⟩
      simp only [← Functor.map_comp_apply, ← op_comp, image.fac]

end SSet.BisimplicialRealization
