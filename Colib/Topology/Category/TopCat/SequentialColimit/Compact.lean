/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Path

/-!
# Compact subsets of sequential topological colimits

For a sequential diagram of T₁ spaces with injective transition maps, every
compact subset of its actual topological colimit is contained in one stage.
The argument uses the final topology, not a local compactness assumption:
a sequence escaping the stages has closed discrete range, because every
subset of that range has finite preimage in each stage.

When the transition maps are closed embeddings, the colimit injections are
also closed embeddings. Thus maps from compact spaces factor continuously
through a stage.
-/
/-!
## Implementation provenance

Adapted from `Quillen/Topology/Realization/CompactStages.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Only namespace and dependency
ownership change. The actual cocone maps, endpoints, universe parameters and
hypotheses are retained. This is a generic sequential-colimit theorem, with
no realization or Theorem A/B assumption.
-/
@[expose] public section

open Topology


noncomputable section

open CategoryTheory Limits

universe u v

namespace TopCat.SequentialColimit

variable {F : ℕ ⥤ TopCat.{u}} {c : Cocone F}

/-- The stage images of any sequential cocone form an increasing family. -/
theorem stageRange_monotone (c : Cocone F) :
    Monotone (fun n : ℕ ↦ (Set.range (c.ι.app n) : Set c.pt)) := by
  intro n m h x hx
  obtain ⟨y, rfl⟩ := hx
  refine ⟨F.map (homOfLE h) y, ?_⟩
  exact ConcreteCategory.congr_hom (c.w (homOfLE h)) y

/-- Every point of an actual topological colimit belongs to a stage. -/
theorem exists_mem_stageRange (hc : IsColimit c) (x : c.pt) :
    ∃ n, x ∈ Set.range (c.ι.app n) := by
  obtain ⟨n, y, hy⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget TopCat) hc) x
  exact ⟨n, y, hy⟩

/-- A finite subset of a sequential colimit is contained in one stage. -/
theorem finite_subset_stageRange (hc : IsColimit c) {s : Set c.pt} (hs : s.Finite) :
    ∃ n, s ⊆ Set.range (c.ι.app n) := by
  classical
  induction s, hs using Set.Finite.induction_on with
  | empty => exact ⟨0, Set.empty_subset _⟩
  | @insert x s hx hs ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨m, hm⟩ := exists_mem_stageRange hc x
    refine ⟨max m n, ?_⟩
    intro y hy
    rcases hy with rfl | hy
    · exact stageRange_monotone c (Nat.le_max_left m n) hm
    · exact stageRange_monotone c (Nat.le_max_right m n) (hn hy)

/-- Injective transition maps give injective maps into the actual colimit. -/
theorem stage_injective (hc : IsColimit c)
    (hF : ∀ {n m : ℕ} (f : n ⟶ m), Function.Injective (F.map f)) (n : ℕ) :
    Function.Injective (c.ι.app n) := by
  intro x y h
  obtain ⟨m, f, hf⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff'
      (isColimitOfPreserves (forget TopCat) hc) x y).mp h
  exact hF f hf

/-- Compact subsets of sequential final-topology colimits of T₁ spaces with
injective structure maps are bounded in the stage index. -/
theorem isCompact_subset_stageRange (hc : IsColimit c)
    [∀ n, T1Space (F.obj n)]
    (hinj : ∀ n, Function.Injective (c.ι.app n))
    {K : Set c.pt} (hK : IsCompact K) :
    ∃ n, K ⊆ Set.range (c.ι.app n) := by
  classical
  by_contra h
  have hchoose : ∀ n, ∃ x, x ∈ K ∧ x ∉ Set.range (c.ι.app n) := by
    simpa only [not_exists, Set.not_subset] using h
  choose x hxK hxout using hchoose
  have hclosed (s : Set c.pt) (hs : s ⊆ Set.range x) : IsClosed s := by
    apply (TopCat.isClosed_iff_of_isColimit c hc s).mpr
    intro n
    have hsub : c.ι.app n ⁻¹' s ⊆
        c.ι.app n ⁻¹' (x '' Set.Iio n) := by
      intro y hy
      obtain ⟨m, hm⟩ := hs hy
      refine ⟨m, ?_, hm⟩
      by_contra hmn
      have hnm : n ≤ m := Nat.le_of_not_gt hmn
      apply hxout m
      exact stageRange_monotone c hnm ⟨y, hm.symm⟩
    exact ((Set.finite_Iio n).image x |>.preimage (hinj n).injOn |>.subset hsub).isClosed
  have hrangeK : Set.range x ⊆ K := by
    rintro _ ⟨n, rfl⟩
    exact hxK n
  have hrange_compact : IsCompact (Set.range x) := by
    simpa only [Set.inter_eq_right.mpr hrangeK] using
      hK.inter_right (hclosed (Set.range x) Set.Subset.rfl)
  have hrange_discrete : IsDiscrete (Set.range x) := by
    apply isDiscrete_iff_forall_mem_exists_isClosed.mpr
    intro s hs
    exact ⟨s, hclosed s hs, Set.inter_eq_left.mpr hs⟩
  obtain ⟨n, hn⟩ := finite_subset_stageRange hc (hrange_compact.finite hrange_discrete)
  exact hxout n (hn ⟨n, rfl⟩)

/-- Closed embeddings at successor stages imply closed embeddings for every
transition in the sequential diagram. -/
theorem transition_isClosedEmbedding
    (hF : ∀ n, IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n))))
    {n m : ℕ} (f : n ⟶ m) : IsClosedEmbedding (F.map f) := by
  have h : n ≤ m := leOfHom f
  have hf : f = homOfLE h := Subsingleton.elim _ _
  subst f
  induction m, h using Nat.le_induction with
  | base => simpa using (IsClosedEmbedding.id : IsClosedEmbedding (id : F.obj n → F.obj n))
  | succ m h ih =>
    have heq : (homOfLE (Nat.le.step h) : n ⟶ m + 1) =
        homOfLE h ≫ homOfLE (Nat.le_succ m) := Subsingleton.elim _ _
    rw [heq, F.map_comp]
    exact (hF m).comp ih

/-- The structure maps of a sequential closed-embedding colimit are themselves
closed embeddings. This establishes the subspace topology needed to lift maps. -/
theorem stage_isClosedEmbedding (hc : IsColimit c)
    (hF : ∀ n, IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n)))) (n : ℕ) :
    IsClosedEmbedding (c.ι.app n) := by
  have hinj := stage_injective hc (fun f ↦ (transition_isClosedEmbedding hF f).injective)
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap
    (c.ι.app n).hom.continuous (hinj n)
  intro s hs
  apply (TopCat.isClosed_iff_of_isColimit c hc _).mpr
  intro m
  rcases le_total n m with h | h
  · have heq : c.ι.app m ⁻¹' (c.ι.app n '' s) = F.map (homOfLE h) '' s := by
      ext y
      constructor
      · rintro ⟨x, hx, hxy⟩
        refine ⟨x, hx, hinj m ?_⟩
        exact (ConcreteCategory.congr_hom (c.w (homOfLE h)) x).trans hxy
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, (ConcreteCategory.congr_hom (c.w (homOfLE h)) x).symm⟩
    rw [heq]
    exact (transition_isClosedEmbedding hF (homOfLE h)).isClosedMap s hs
  · have heq : c.ι.app m ⁻¹' (c.ι.app n '' s) = F.map (homOfLE h) ⁻¹' s := by
      ext y
      constructor
      · rintro ⟨x, hx, hxy⟩
        have he : F.map (homOfLE h) y = x := hinj n
          ((ConcreteCategory.congr_hom (c.w (homOfLE h)) y).trans hxy.symm)
        simpa only [Set.mem_preimage, he] using hx
      · intro hy
        exact ⟨F.map (homOfLE h) y, hy,
          ConcreteCategory.congr_hom (c.w (homOfLE h)) y⟩
    rw [heq]
    exact hs.preimage (F.map (homOfLE h)).hom.continuous

/-- The actual sequential colimit of T₁ spaces and closed embeddings is T₁. -/
theorem t1Space_colimit (hc : IsColimit c) [∀ n, T1Space (F.obj n)]
    (hF : ∀ n, IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n)))) :
    T1Space c.pt where
  t1 x := by
    apply (TopCat.isClosed_iff_of_isColimit c hc _).mpr
    intro n
    exact ((Set.finite_singleton x).preimage
      (stage_isClosedEmbedding hc hF n).injective.injOn).isClosed

/-- Every compact subset of a sequential colimit of T₁ spaces and closed
embeddings lies in one stage. Only the successor maps are assumptions. -/
theorem isCompact_subset_stageRange_of_closedEmbeddings (hc : IsColimit c)
    [∀ n, T1Space (F.obj n)]
    (hF : ∀ n, IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n))))
    {K : Set c.pt} (hK : IsCompact K) :
    ∃ n, K ⊆ Set.range (c.ι.app n) :=
  isCompact_subset_stageRange hc (fun n ↦ (stage_isClosedEmbedding hc hF n).injective) hK

/-- A map from any compact space into the actual sequential colimit of T₁
spaces and closed embeddings factors continuously through a stage. -/
theorem continuousMap_factors (hc : IsColimit c)
    [∀ n, T1Space (F.obj n)]
    (hF : ∀ n, IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n))))
    {X : Type v} [TopologicalSpace X] [CompactSpace X] (f : C(X, c.pt)) :
    ∃ n, ∃ g : C(X, F.obj n), ∀ x, c.ι.app n (g x) = f x := by
  classical
  obtain ⟨n, hn⟩ := isCompact_subset_stageRange_of_closedEmbeddings hc hF
    (isCompact_range f.continuous)
  have hchoose : ∀ x, ∃ y, c.ι.app n y = f x := fun x ↦ hn ⟨x, rfl⟩
  choose g hg using hchoose
  have hg_cont : Continuous g := by
    apply (stage_isClosedEmbedding hc hF n).isInducing.continuous_iff.mpr
    have heq : (c.ι.app n : F.obj n → c.pt) ∘ g = f := funext hg
    rw [heq]
    exact f.continuous
  exact ⟨n, ⟨g, hg_cont⟩, hg⟩

/-- Categorical form of compact-source continuous factorization. -/
theorem hom_factors (hc : IsColimit c)
    [∀ n, T1Space (F.obj n)]
    (hF : ∀ n, IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n))))
    {X : TopCat.{u}} [CompactSpace X] (f : X ⟶ c.pt) :
    ∃ n, ∃ g : X ⟶ F.obj n, g ≫ c.ι.app n = f := by
  obtain ⟨n, g, hg⟩ := continuousMap_factors hc hF f.hom
  refine ⟨n, TopCat.ofHom g, ?_⟩
  ext x
  exact hg x

/-- Compact-source factorization can be taken beyond any prescribed stage. -/
theorem continuousMap_factors_above (hc : IsColimit c)
    [∀ n, T1Space (F.obj n)]
    (hF : ∀ n, IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n))))
    {X : Type v} [TopologicalSpace X] [CompactSpace X] (f : C(X, c.pt)) (k : ℕ) :
    ∃ n, k ≤ n ∧ ∃ g : C(X, F.obj n), ∀ x, c.ι.app n (g x) = f x := by
  obtain ⟨m, g, hg⟩ := continuousMap_factors hc hF f
  let h : m ≤ max k m := Nat.le_max_right k m
  refine ⟨max k m, Nat.le_max_left k m, (F.map (homOfLE h)).hom.comp g, ?_⟩
  intro x
  exact (ConcreteCategory.congr_hom (c.w (homOfLE h)) (g x)).trans (hg x)

/-- A path between points of stage `k` lifts to a path in some later stage,
with exactly the transported endpoints. -/
theorem path_factors (hc : IsColimit c)
    [∀ n, T1Space (F.obj n)]
    (hF : ∀ n, IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n))))
    (k : ℕ) {x y : F.obj k} (p : Path (c.ι.app k x) (c.ι.app k y)) :
    ∃ n, ∃ h : k ≤ n,
      ∃ q : Path (F.map (homOfLE h) x) (F.map (homOfLE h) y),
        ∀ t, c.ι.app n (q t) = p t := by
  obtain ⟨n, h, g, hg⟩ := continuousMap_factors_above hc hF p.toContinuousMap k
  have hinj := (stage_isClosedEmbedding hc hF n).injective
  refine ⟨n, h, { toContinuousMap := g, source' := ?_, target' := ?_ }, hg⟩
  · apply hinj
    exact (hg 0).trans (p.source.trans
      (ConcreteCategory.congr_hom (c.w (homOfLE h)) x).symm)
  · apply hinj
    exact (hg 1).trans (p.target.trans
      (ConcreteCategory.congr_hom (c.w (homOfLE h)) y).symm)

end TopCat.SequentialColimit

attribute [colib_tag "COL-0088",
  colib_ref "DuggerIsaksenHypercovers" "Appendix A, Lemma A.3 and preceding paragraph, pages 17-18"
    "specialization"
    "Compact-source factorization for T1 stages and successor closed embeddings"]
  TopCat.SequentialColimit.isCompact_subset_stageRange_of_closedEmbeddings
  TopCat.SequentialColimit.continuousMap_factors
  TopCat.SequentialColimit.hom_factors
  TopCat.SequentialColimit.continuousMap_factors_above
  TopCat.SequentialColimit.path_factors

attribute [colib_tag "COL-0088",
  colib_ref "DuggerIsaksenHypercovers" "Appendix A, discussion preceding Lemma A.3, page 17"
    "background"
    "Final-topology compact containment and stage embeddings under separate hypotheses"]
  TopCat.SequentialColimit.isCompact_subset_stageRange
  TopCat.SequentialColimit.stage_isClosedEmbedding
  TopCat.SequentialColimit.t1Space_colimit
