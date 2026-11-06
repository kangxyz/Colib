/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.FiniteSubcomplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable

/-!
# Compact maps and equalities in filtered simplicial realization colimits

Genuinely finite subcomplex support and finite simplicial presentability
supply exact stage factorization. Equal continuous maps are detected later
by factoring a finite simplicial source through its finite image in the
colimit, whose realization is an embedding.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/FilteredRealization/Compact.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The arbitrary filtered category,
actual cocone maps, exact factorization and universe parameters are retained. -/
@[expose] public section

open Topology

noncomputable section
open CategoryTheory Limits SSet
open scoped Simplicial unitInterval
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Topology.FilteredRealization
variable {J : Type u} [SmallCategory J] [IsFiltered J]
  (F : J ⥤ SSet.{u}) (c : Cocone F) (hc : IsColimit c)
include hc

/-- A map from any compact space into an actual filtered simplicial colimit
realization factors continuously and exactly through one original stage. -/
theorem compact_factors {T : Type v} [TopologicalSpace T] [CompactSpace T]
    (f : C(T, |c.pt|)) :
    ∃ j, ∃ g : C(T, |F.obj j|), (SSet.toTop.map (c.ι.app j)).hom.comp g = f := by
  obtain ⟨A, hA, g, hg⟩ := realization_continuousMap_factors_finiteSubcomplex f
  let : SSet.Finite A := hA
  obtain ⟨j, a, ha⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hc A.ι
  refine ⟨j, (SSet.toTop.map a).hom.comp g, ?_⟩
  rw [← ContinuousMap.comp_assoc, ← TopCat.hom_comp, ← Functor.map_comp, ha]
  exact hg

/-- A finite source at one stage eventually factors through its actual
simplicial image in the colimit. -/
theorem finite_source_compression {A : SSet.{u}} [A.Finite] (j : J) (a : A ⟶ F.obj j) :
    ∃ k, ∃ u : j ⟶ k,
      ∃ b : (SSet.Subcomplex.range (a ≫ c.ι.app j) : SSet.{u}) ⟶ F.obj k,
        a ≫ F.map u = SSet.Subcomplex.toRange (a ≫ c.ι.app j) ≫ b := by
  let R := SSet.Subcomplex.range (a ≫ c.ι.app j)
  obtain ⟨l, b, hb⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hc R.ι
  have he : a ≫ c.ι.app j = (SSet.Subcomplex.toRange (a ≫ c.ι.app j) ≫ b) ≫ c.ι.app l := by
    rw [Category.assoc, hb]
    rfl
  obtain ⟨k, u, v, huv⟩ := IsFinitelyPresentable.exists_eq_of_isColimit hc a
    (SSet.Subcomplex.toRange (a ≫ c.ι.app j) ≫ b) he
  exact ⟨k, u, b ≫ F.map v, by simpa only [Category.assoc] using huv⟩

/-- Equality of compact-source continuous maps at one stage is eventually
literal equality. This uses finite image compression and does not assume
that the original stage-to-colimit maps are injective. -/
theorem compact_eq_eventually {T : Type v} [TopologicalSpace T] [CompactSpace T]
    (j : J) (f g : C(T, |F.obj j|))
    (he : (SSet.toTop.map (c.ι.app j)).hom.comp f =
      (SSet.toTop.map (c.ι.app j)).hom.comp g) :
    ∃ k, ∃ u : j ⟶ k, (SSet.toTop.map (F.map u)).hom.comp f =
      (SSet.toTop.map (F.map u)).hom.comp g := by
  let a : C(T ⊕ T, |F.obj j|) :=
    ⟨Sum.elim f g, f.continuous.sumElim g.continuous⟩
  obtain ⟨A, hA, b, hb⟩ := realization_continuousMap_factors_finiteSubcomplex a
  let : SSet.Finite A := hA
  obtain ⟨k, u, r, hr⟩ := finite_source_compression F c hc j A.ι
  have hb0 (t : T) : SSet.toTop.map A.ι (b (Sum.inl t)) = f t := ContinuousMap.congr_fun hb _
  have hb1 (t : T) : SSet.toTop.map A.ι (b (Sum.inr t)) = g t := ContinuousMap.congr_fun hb _
  let R := SSet.Subcomplex.range (A.ι ≫ c.ι.app j)
  let π := SSet.Subcomplex.toRange (A.ι ≫ c.ι.app j)
  have hπ (t : T) : SSet.toTop.map π (b (Sum.inl t)) = SSet.toTop.map π (b (Sum.inr t)) := by
    apply (realization_mono_isClosedEmbedding R.ι).injective
    change (SSet.toTop.map π ≫ SSet.toTop.map R.ι) (b (Sum.inl t)) =
      (SSet.toTop.map π ≫ SSet.toTop.map R.ι) (b (Sum.inr t))
    rw [← Functor.map_comp]
    change SSet.toTop.map (A.ι ≫ c.ι.app j) (b (Sum.inl t)) =
      SSet.toTop.map (A.ι ≫ c.ι.app j) (b (Sum.inr t))
    rw [Functor.map_comp]
    change SSet.toTop.map (c.ι.app j) (SSet.toTop.map A.ι (b (Sum.inl t))) =
      SSet.toTop.map (c.ι.app j) (SSet.toTop.map A.ι (b (Sum.inr t)))
    rw [hb0, hb1]
    exact ContinuousMap.congr_fun he t
  refine ⟨k, u, ContinuousMap.ext (fun t ↦ ?_)⟩
  change SSet.toTop.map (F.map u) (f t) = SSet.toTop.map (F.map u) (g t)
  rw [← show SSet.toTop.map A.ι (b (Sum.inl t)) = f t from ContinuousMap.congr_fun hb _,
    ← show SSet.toTop.map A.ι (b (Sum.inr t)) = g t from ContinuousMap.congr_fun hb _]
  change (SSet.toTop.map A.ι ≫ SSet.toTop.map (F.map u)) (b (Sum.inl t)) =
    (SSet.toTop.map A.ι ≫ SSet.toTop.map (F.map u)) (b (Sum.inr t))
  rw [← Functor.map_comp, hr, Functor.map_comp]
  exact congrArg (SSet.toTop.map r) (hπ t)

end Topology.FilteredRealization
