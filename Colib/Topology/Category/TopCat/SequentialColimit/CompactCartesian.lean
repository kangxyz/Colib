/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Category.TopCat.SequentialColimit.Compact
public import Colib.Topology.HomotopyPullback.Basic
public import Colib.Topology.Homotopy.HomotopyGroup.Equivalence

/-!
# Compact tests for sequential homotopy-cartesian assembly

For sequential closed-embedding diagrams of T₁ spaces, a compact family in
an actual stage-to-colimit homotopy pullback factors through a finite-stage
homotopy pullback. Both the source coordinate and the entire family of paths
are factored, so this is stronger than a pointwise factorization statement.
The resulting assembly theorem concerns maps from compact parameter spaces;
it does not assert a global homotopy equivalence.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/SequentialColimit/CompactCartesian.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual cocone and path-space maps,
compact parameter spaces, relative homotopies and all degrees are retained. -/
@[expose] public section

open Topology

noncomputable section
open CategoryTheory Limits
open scoped unitInterval

universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Topology.HomotopyPullback.Sequential

variable {F G : ℕ ⥤ TopCat.{u}} (η : F ⟶ G)
  (c : Cocone F) (hc : IsColimit c) (d : Cocone G)

/-- The homotopy pullback comparing stage `k` to a later finite stage. -/
abbrev StagePullback (k n : ℕ) (h : k ≤ n) :=
  HomotopyPullback (η.app n).hom (G.map (homOfLE h)).hom

/-- The actual homotopy pullback comparing a stage to the colimit. -/
abbrev ColimitPullback (k : ℕ) :=
  HomotopyPullback (hc.map d η).hom (d.ι.app k).hom

/-- The finite-stage canonical constant-path comparison. -/
def stageComparison (k n : ℕ) (h : k ≤ n) :
    C(F.obj k, StagePullback η k n h) :=
  HomotopyPullback.comparison _ _ (η.app k).hom (F.map (homOfLE h)).hom
    (congrArg TopCat.Hom.hom (η.naturality (homOfLE h)))

/-- The canonical comparison to the actual colimit homotopy pullback. -/
def colimitComparison (k : ℕ) : C(F.obj k, ColimitPullback η c hc d k) :=
  HomotopyPullback.comparison _ _ (η.app k).hom (c.ι.app k).hom
    (congrArg TopCat.Hom.hom (hc.ι_map d η k))

/-- Send a finite-stage pullback to the colimit by mapping its source and
its entire path through the respective cocone maps. -/
def stageToColimit (k n : ℕ) (h : k ≤ n) :
    C(StagePullback η k n h, ColimitPullback η c hc d k) where
  toFun z := ⟨(z.1.1, c.ι.app n z.1.2.1, (d.ι.app n).hom.comp z.1.2.2),
    (congrArg (d.ι.app n) z.2.1).trans
      (ConcreteCategory.congr_hom (hc.ι_map d η n) z.1.2.1).symm,
    (congrArg (d.ι.app n) z.2.2).trans
      (ConcreteCategory.congr_hom (d.w (homOfLE h)) z.1.1)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · apply Continuous.prodMk
      · fun_prop
      · apply ContinuousMap.continuous_of_continuous_uncurry
        change Continuous (fun z : StagePullback η k n h × unitInterval ↦
          d.ι.app n (z.1.1.2.2 z.2))
        fun_prop

@[simp]
theorem stageToColimit_comparison (k n : ℕ) (h : k ≤ n) :
    (stageToColimit η c hc d k n h).comp (stageComparison η k n h) =
      colimitComparison η c hc d k := by
  ext x
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact ConcreteCategory.congr_hom (c.w (homOfLE h)) x
    · apply ContinuousMap.ext
      intro t
      exact ConcreteCategory.congr_hom (d.w (homOfLE h)) (η.app k x)

/-- Injectivity at each stage is also injectivity on path-space pullbacks. -/
theorem stageToColimit_injective (k n : ℕ) (h : k ≤ n)
    (hF : Function.Injective (c.ι.app n)) (hG : Function.Injective (d.ι.app n)) :
    Function.Injective (stageToColimit η c hc d k n h) := by
  intro x y he
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun z : ColimitPullback η c hc d k ↦ z.1.1) he
  · apply Prod.ext
    · exact hF (congrArg (fun z : ColimitPullback η c hc d k ↦ z.1.2.1) he)
    · apply ContinuousMap.ext
      intro t
      exact hG (congrArg (fun z : ColimitPullback η c hc d k ↦ z.1.2.2 t) he)

variable (hd : IsColimit d) [∀ n, T1Space (F.obj n)] [∀ n, T1Space (G.obj n)]
  (hF : ∀ n, IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n))))
  (hG : ∀ n, IsClosedEmbedding (G.map (homOfLE (Nat.le_succ n))))

include hd hF hG in
/-- Every compact family in the actual colimit homotopy pullback factors
through one later finite-stage homotopy pullback. The chosen base coordinate
at stage `k` is retained exactly. -/
theorem compact_factors {X : Type v} [TopologicalSpace X] [CompactSpace X]
    (k : ℕ) (f : C(X, ColimitPullback η c hc d k)) :
    ∃ n, ∃ h : k ≤ n, ∃ g : C(X, StagePullback η k n h),
      (stageToColimit η c hc d k n h).comp g = f := by
  obtain ⟨m, hm, a, ha⟩ := TopCat.SequentialColimit.continuousMap_factors_above hc hF
    ((HomotopyPullback.sourceProjection _ _).comp f) k
  let paths : C(X × unitInterval, d.pt) := ⟨fun z ↦ (f z.1).1.2.2 z.2, by fun_prop⟩
  obtain ⟨n, hn, b, hb⟩ := TopCat.SequentialColimit.continuousMap_factors_above hd hG paths m
  let h : k ≤ n := hm.trans hn
  let a' : C(X, F.obj n) := (F.map (homOfLE hn)).hom.comp a
  have ha' (x : X) : c.ι.app n (a' x) = (f x).1.2.1 :=
    (ConcreteCategory.congr_hom (c.w (homOfLE hn)) (a x)).trans (ha x)
  have hinj := (TopCat.SequentialColimit.stage_isClosedEmbedding hd hG n).injective
  have hzero (x : X) : b (x, 0) = η.app n (a' x) := by
    apply hinj
    calc
      d.ι.app n (b (x, 0)) = (f x).1.2.2 0 := hb (x, 0)
      _ = hc.map d η ((f x).1.2.1) := (f x).2.1
      _ = hc.map d η (c.ι.app n (a' x)) := congrArg (hc.map d η) (ha' x).symm
      _ = d.ι.app n (η.app n (a' x)) := ConcreteCategory.congr_hom (hc.ι_map d η n) _
  have hone (x : X) : b (x, 1) = G.map (homOfLE h) (f x).1.1 := by
    apply hinj
    exact (hb (x, 1)).trans ((f x).2.2.trans
      (ConcreteCategory.congr_hom (d.w (homOfLE h)) (f x).1.1).symm)
  let g : C(X, StagePullback η k n h) := {
    toFun x := ⟨((f x).1.1, a' x, ⟨fun t ↦ b (x, t), by fun_prop⟩), hzero x, hone x⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.prodMk
      · fun_prop
      · apply Continuous.prodMk a'.continuous
        apply ContinuousMap.continuous_of_continuous_uncurry
        exact b.continuous }
  refine ⟨n, h, g, ?_⟩
  ext x
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact ha' x
    · apply ContinuousMap.ext
      intro t
      exact hb (x, t)

include hd hF hG in
/-- Homotopies from compact parameter spaces lift to one finite-stage
pullback, retaining any specified fixed subset and both endpoint maps. -/
theorem compact_homotopyRel_factors {X : Type v} [TopologicalSpace X] [CompactSpace X]
    (k : ℕ) {a b : C(X, F.obj k)} (S : Set X)
    (H : ((colimitComparison η c hc d k).comp a).HomotopyRel
      ((colimitComparison η c hc d k).comp b) S) :
    ∃ n, ∃ h : k ≤ n,
      Nonempty (((stageComparison η k n h).comp a).HomotopyRel
        ((stageComparison η k n h).comp b) S) := by
  obtain ⟨n, h, g, hg⟩ := compact_factors η c hc d hd hF hG k H.toContinuousMap
  have hi := stageToColimit_injective η c hc d k n h
    (TopCat.SequentialColimit.stage_isClosedEmbedding hc hF n).injective
    (TopCat.SequentialColimit.stage_isClosedEmbedding hd hG n).injective
  have hcomp (x : F.obj k) :
      stageToColimit η c hc d k n h (stageComparison η k n h x) =
        colimitComparison η c hc d k x :=
    ContinuousMap.congr_fun (stageToColimit_comparison η c hc d k n h) x
  refine ⟨n, h, ⟨{
    toContinuousMap := g
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }⟩⟩
  · intro x
    apply hi
    exact (ContinuousMap.congr_fun hg (0, x)).trans
      ((H.map_zero_left x).trans (hcomp (a x)).symm)
  · intro x
    apply hi
    exact (ContinuousMap.congr_fun hg (1, x)).trans
      ((H.map_one_left x).trans (hcomp (b x)).symm)
  · intro t x hx
    apply hi
    exact (ContinuousMap.congr_fun hg (t, x)).trans
      ((H.prop t x hx).trans (hcomp (a x)).symm)

include hd hF hG in
/-- Finite-stage cartesianness gives surjectivity on homotopy classes of
maps from every compact parameter space. -/
theorem compact_homotopy_surjective (k : ℕ)
    (e : ∀ n (h : k ≤ n), ContinuousMap.HomotopyEquiv (F.obj k) (StagePullback η k n h))
    (he : ∀ n h, (e n h).toFun = stageComparison η k n h)
    {X : Type v} [TopologicalSpace X] [CompactSpace X]
    (f : C(X, ColimitPullback η c hc d k)) :
    ∃ a : C(X, F.obj k), ((colimitComparison η c hc d k).comp a).Homotopic f := by
  obtain ⟨n, h, g, hg⟩ := compact_factors η c hc d hd hF hG k f
  refine ⟨(e n h).invFun.comp g, ?_⟩
  have H := (ContinuousMap.Homotopic.refl (stageToColimit η c hc d k n h)).comp
    ((e n h).right_inv.comp (ContinuousMap.Homotopic.refl g))
  simpa only [he n h, ← ContinuousMap.comp_assoc, stageToColimit_comparison,
    ContinuousMap.id_comp, hg] using H

include hd hF hG in
/-- Every component of the actual colimit pullback is reached by the canonical
comparison. A constant compact test supplies a source point even when no
nonemptiness assumption on the stage has been made. -/
theorem colimitComparison_component_surjective (k : ℕ)
    (e : ∀ n (h : k ≤ n), ContinuousMap.HomotopyEquiv (F.obj k) (StagePullback η k n h))
    (he : ∀ n h, (e n h).toFun = stageComparison η k n h)
    (y : ColimitPullback η c hc d k) :
    ∃ x : F.obj k, Joined (colimitComparison η c hc d k x) y := by
  obtain ⟨a, ⟨H⟩⟩ := compact_homotopy_surjective η c hc d hd hF hG k e he
    (ContinuousMap.const PUnit.{u + 1} y)
  exact ⟨a PUnit.unit, ⟨H.evalAt PUnit.unit⟩⟩

include hd hF hG in
/-- Finite-stage cartesianness also detects homotopies on all compact
parameter spaces. -/
theorem compact_homotopy_injective (k : ℕ)
    (e : ∀ n (h : k ≤ n), ContinuousMap.HomotopyEquiv (F.obj k) (StagePullback η k n h))
    (he : ∀ n h, (e n h).toFun = stageComparison η k n h)
    {X : Type v} [TopologicalSpace X] [CompactSpace X]
    {a b : C(X, F.obj k)}
    (H : ((colimitComparison η c hc d k).comp a).Homotopic
      ((colimitComparison η c hc d k).comp b)) : a.Homotopic b := by
  let Hrel : ((colimitComparison η c hc d k).comp a).HomotopyRel
      ((colimitComparison η c hc d k).comp b) ∅ := {
    toHomotopy := H.some
    prop' := by simp }
  obtain ⟨n, h, Hn⟩ := compact_homotopyRel_factors η c hc d hd hF hG k ∅ Hrel
  have H' : ((e n h).toFun.comp a).Homotopic ((e n h).toFun.comp b) := by
    simpa only [he n h] using (show ((stageComparison η k n h).comp a).Homotopic
      ((stageComparison η k n h).comp b) from ⟨Hn.some.toHomotopy⟩)
  have Ha := (e n h).left_inv.comp (ContinuousMap.Homotopic.refl a)
  have Hb := (e n h).left_inv.comp (ContinuousMap.Homotopic.refl b)
  exact Ha.symm.trans (((ContinuousMap.Homotopic.refl (e n h).invFun).comp H').trans Hb)

include hd hF hG in
/-- Generalized based loops factor through a finite-stage pullback while
retaining their entire cube-boundary condition. -/
theorem genLoop_factors {N : Type v} (k : ℕ) (x : F.obj k)
    (p : GenLoop N (ColimitPullback η c hc d k) (colimitComparison η c hc d k x)) :
    ∃ n, ∃ h : k ≤ n,
      ∃ q : GenLoop N (StagePullback η k n h) (stageComparison η k n h x),
        ∀ t, stageToColimit η c hc d k n h (q t) = p t := by
  obtain ⟨n, h, g, hg⟩ := compact_factors η c hc d hd hF hG k p.val
  have hi := stageToColimit_injective η c hc d k n h
    (TopCat.SequentialColimit.stage_isClosedEmbedding hc hF n).injective
    (TopCat.SequentialColimit.stage_isClosedEmbedding hd hG n).injective
  refine ⟨n, h, ⟨g, ?_⟩, fun t ↦ ContinuousMap.congr_fun hg t⟩
  intro t ht
  apply hi
  exact (ContinuousMap.congr_fun hg t).trans ((GenLoop.boundary p t ht).trans
    (ContinuousMap.congr_fun (stageToColimit_comparison η c hc d k n h) x).symm)

include hd hF hG in
/-- Actual finite-stage homotopy-cartesian comparisons imply bijectivity of
the canonical stage-to-colimit map on every positive-dimensional homotopy
group. This is a weak comparison theorem, not a global homotopy equivalence.
Neither the colimit comparison nor its induced isomorphisms are hypotheses. -/
theorem colimitComparison_piMap_bijective (k : ℕ)
    (e : ∀ n (h : k ≤ n), ContinuousMap.HomotopyEquiv (F.obj k) (StagePullback η k n h))
    (he : ∀ n h, (e n h).toFun = stageComparison η k n h)
    (x : F.obj k) (q : ℕ) :
    Function.Bijective (HomotopyGroup.piMap q (colimitComparison η c hc d k) (x := x) rfl) := by
  have hstage (n : ℕ) (h : k ≤ n) :
      Function.Bijective (HomotopyGroup.piMap q (stageComparison η k n h) (x := x) rfl) := by
    let E : ContinuousMap.HomotopyEquiv (F.obj k) (StagePullback η k n h) := {
      e n h with
      toFun := stageComparison η k n h
      left_inv := by simpa only [he n h] using (e n h).left_inv
      right_inv := by simpa only [he n h] using (e n h).right_inv }
    exact piMap_bijective_of_homotopyEquiv E (x := x) rfl q
  constructor
  · intro a b hab
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
        obtain ⟨H⟩ := Quotient.exact hab
        obtain ⟨n, h, Hn⟩ := compact_homotopyRel_factors η c hc d hd hF hG k
          (Cube.boundary (Fin (q + 1))) H
        apply (hstage n h).1
        exact Quotient.sound Hn
  · intro a
    induction a using Quotient.inductionOn with | h p =>
      obtain ⟨n, h, pg, hpg⟩ := genLoop_factors η c hc d hd hF hG k x p
      obtain ⟨a, ha⟩ := (hstage n h).2 (Quotient.mk' pg)
      let j := stageToColimit η c hc d k n h
      have hj : j (stageComparison η k n h x) = colimitComparison η c hc d k x :=
        ContinuousMap.congr_fun (stageToColimit_comparison η c hc d k n h) x
      refine ⟨a, ?_⟩
      have hmap : HomotopyGroup.map j hj (Quotient.mk' pg) = Quotient.mk' p := by
        apply congrArg Quotient.mk'
        exact GenLoop.ext _ _ hpg
      have hcomp := HomotopyGroup.map_comp (N := Fin (q + 1))
        (stageComparison η k n h) (x := x) rfl j hj a
      have hcomp' : HomotopyGroup.map (colimitComparison η c hc d k) rfl a =
          HomotopyGroup.map j hj (HomotopyGroup.map (stageComparison η k n h) rfl a) := by
        simpa only [j, stageToColimit_comparison] using hcomp
      exact hcomp'.trans ((congrArg (HomotopyGroup.map j hj) ha).trans hmap)

include hd hF hG in
/-- The actual canonical comparison also induces a bijection on the zeroth
homotopy set, including components not containing the chosen point. -/
theorem colimitComparison_piZero_bijective (k : ℕ)
    (e : ∀ n (h : k ≤ n), ContinuousMap.HomotopyEquiv (F.obj k) (StagePullback η k n h))
    (he : ∀ n h, (e n h).toFun = stageComparison η k n h)
    (x : F.obj k) :
    Function.Bijective (HomotopyGroup.map (N := Fin 0)
      (colimitComparison η c hc d k) (x := x) rfl) := by
  constructor
  · intro a b hab
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
        obtain ⟨H⟩ := Quotient.exact hab
        obtain ⟨K⟩ := compact_homotopy_injective η c hc d hd hF hG k e he
          (show ((colimitComparison η c hc d k).comp a.val).Homotopic
            ((colimitComparison η c hc d k).comp b.val) from ⟨H.toHomotopy⟩)
        exact Quotient.sound ⟨{
          toHomotopy := K
          prop' := by rintro t z ⟨i, _⟩; exact Fin.elim0 i }⟩
  · intro a
    induction a using Quotient.inductionOn with | h p =>
      obtain ⟨g, H⟩ := compact_homotopy_surjective η c hc d hd hF hG k e he p.val
      let pg : GenLoop (Fin 0) (F.obj k) x :=
        ⟨g, by rintro z ⟨i, _⟩; exact Fin.elim0 i⟩
      refine ⟨Quotient.mk' pg, Quotient.sound ⟨?_⟩⟩
      exact {
        toHomotopy := H.some
        prop' := by rintro t z ⟨i, _⟩; exact Fin.elim0 i }

include hd hF hG in
/-- Sequential cartesian assembly on every actual finite-dimensional
homotopy set. The degree-zero statement and all based group statements use
the same specified stage-to-colimit comparison map. -/
theorem colimitComparison_homotopyGroupMap_bijective (k : ℕ)
    (e : ∀ n (h : k ≤ n), ContinuousMap.HomotopyEquiv (F.obj k) (StagePullback η k n h))
    (he : ∀ n h, (e n h).toFun = stageComparison η k n h)
    (x : F.obj k) (q : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin q)
      (colimitComparison η c hc d k) (x := x) rfl) := by
  cases q with
  | zero => exact colimitComparison_piZero_bijective η c hc d hd hF hG k e he x
  | succ q => exact colimitComparison_piMap_bijective η c hc d hd hF hG k e he x q

/-- The canonical based group isomorphism furnished by compact sequential
assembly; its forward homomorphism remains the specified comparison. -/
def colimitComparisonPiEquiv (k : ℕ)
    (e : ∀ n (h : k ≤ n), ContinuousMap.HomotopyEquiv (F.obj k) (StagePullback η k n h))
    (he : ∀ n h, (e n h).toFun = stageComparison η k n h)
    (x : F.obj k) (q : ℕ) :
    HomotopyGroup.Pi (q + 1) (F.obj k) x ≃*
      HomotopyGroup.Pi (q + 1) (ColimitPullback η c hc d k) (colimitComparison η c hc d k x) :=
  MulEquiv.ofBijective (HomotopyGroup.piMap q (colimitComparison η c hc d k) rfl)
    (colimitComparison_piMap_bijective η c hc d hd hF hG k e he x q)

/-- The forward homomorphism is induced by the specified colimit comparison. -/
@[simp] theorem colimitComparisonPiEquiv_coe (k : ℕ)
    (e : ∀ n (h : k ≤ n), ContinuousMap.HomotopyEquiv (F.obj k) (StagePullback η k n h))
    (he : ∀ n h, (e n h).toFun = stageComparison η k n h)
    (x : F.obj k) (q : ℕ) :
    (colimitComparisonPiEquiv η c hc d hd hF hG k e he x q :
      HomotopyGroup.Pi (q + 1) (F.obj k) x →*
        HomotopyGroup.Pi (q + 1) (ColimitPullback η c hc d k)
          (colimitComparison η c hc d k x)) =
      HomotopyGroup.piMap q (colimitComparison η c hc d k) rfl := rfl

end Topology.HomotopyPullback.Sequential
