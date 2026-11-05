/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.MonomorphismEmbedding
public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits

/-!
# Finite subcomplex support in geometric realization

The relevant finiteness is the number of nondegenerate simplices, not the
skeletal dimension. Realized subcomplex intersections are computed from
actual union pushouts and their injective inclusions.
-/
@[expose] public section

noncomputable section
open CategoryTheory Limits Topology Opposite
open scoped Simplicial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SSet
variable {X : SSet.{u}}

/-- The actual image of a realized simplicial subcomplex. -/
def realizationSubcomplexRange (A : X.Subcomplex) : Set |X| :=
  Set.range (SSet.toTop.map A.ι)

/-- Subcomplex containment gives containment of actual realized images. -/
theorem realizationSubcomplexRange_monotone :
    Monotone (realizationSubcomplexRange (X := X)) := by
  intro A B h x hx
  obtain ⟨a, rfl⟩ := hx
  refine ⟨SSet.toTop.map (SSet.Subcomplex.homOfLE h) a, ?_⟩
  change (SSet.toTop.map (SSet.Subcomplex.homOfLE h) ≫ SSet.toTop.map B.ι) a = _
  rw [← Functor.map_comp]
  rfl

/-- Actual realized intersections follow from the genuine union pushout.
No preservation of arbitrary topological pullbacks is used. -/
theorem realizationSubcomplexRange_inf (A B : X.Subcomplex) :
    realizationSubcomplexRange (A ⊓ B) =
      realizationSubcomplexRange A ∩ realizationSubcomplexRange B := by
  apply Set.Subset.antisymm
  · exact fun _ h ↦ ⟨realizationSubcomplexRange_monotone inf_le_left h,
      realizationSubcomplexRange_monotone inf_le_right h⟩
  · rintro x ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    have sq := (SSet.Subcomplex.BicartSq.isPushout
      (show SSet.Subcomplex.BicartSq (A ⊓ B) A B (A ⊔ B) from ⟨rfl, rfl⟩)).map SSet.toTop
    have hab : SSet.toTop.map (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B)) a =
        SSet.toTop.map (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B)) b := by
      apply (realization_mono_isClosedEmbedding (A ⊔ B).ι).injective
      change (SSet.toTop.map (SSet.Subcomplex.homOfLE le_sup_left) ≫ SSet.toTop.map (A ⊔ B).ι) a =
        (SSet.toTop.map (SSet.Subcomplex.homOfLE le_sup_right) ≫ SSet.toTop.map (A ⊔ B).ι) b
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact ha.trans hb.symm
    obtain ⟨z, hz, _⟩ := (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
      (sq.map (forget TopCat)).isColimit
      (realization_mono_isClosedEmbedding (SSet.Subcomplex.homOfLE
        (inf_le_left : A ⊓ B ≤ A))).injective a b).mp hab
    refine ⟨z, ?_⟩
    calc
      SSet.toTop.map (A ⊓ B).ι z =
          SSet.toTop.map A.ι (SSet.toTop.map (SSet.Subcomplex.homOfLE inf_le_left) z) := by
        change _ = (SSet.toTop.map (SSet.Subcomplex.homOfLE inf_le_left) ≫ SSet.toTop.map A.ι) z
        rw [← Functor.map_comp]
        rfl
      _ = SSet.toTop.map A.ι a := congrArg (SSet.toTop.map A.ι) hz
      _ = x := ha

/-- A finite simplicial set has only finitely many subcomplexes: a subcomplex
is determined by which of its finitely many nondegenerate simplices it contains. -/
instance finite_subcomplex_of_finite (A : SSet.{u}) [A.Finite] : Finite A.Subcomplex := by
  let code : A.Subcomplex → Set A.N := fun B ↦ {s | s.simplex ∈ B.obj _}
  apply Finite.of_injective code
  intro B C h
  apply le_antisymm
  · apply (SSet.Subcomplex.le_iff_contains_nonDegenerate B C).2
    intro n x hx
    have hh : SSet.N.mk x.1 x.2 ∈ code C := by rw [← h]; exact hx
    exact hh
  · apply (SSet.Subcomplex.le_iff_contains_nonDegenerate C B).2
    intro n x hx
    have hh : SSet.N.mk x.1 x.2 ∈ code B := by rw [h]; exact hx
    exact hh

/-- The interval of all subcomplexes below a finite subcomplex is finite. -/
instance finite_subcomplex_Iic (A : X.Subcomplex) [SSet.Finite A] : Finite (Set.Iic A) := by
  let φ : Set.Iic A → (A : SSet.{u}).Subcomplex := fun B ↦ B.1.preimage A.ι
  apply Finite.of_injective φ
  intro B C h
  apply Subtype.ext
  apply le_antisymm
  · intro p x hx
    have hh : (⟨x, B.2 p hx⟩ : A.obj p) ∈ (φ B).obj p := hx
    rw [h] at hh
    exact hh
  · intro p x hx
    have hh : (⟨x, C.2 p hx⟩ : A.obj p) ∈ (φ C).obj p := hx
    rw [← h] at hh
    exact hh

/-- Each actual realization point has some finite simplicial support. -/
theorem realization_exists_finite_subcomplex (x : |X|) :
    ∃ A : X.Subcomplex, SSet.Finite A ∧ x ∈ realizationSubcomplexRange A := by
  obtain ⟨n, f, t, ht⟩ := realization_exists_simplex x
  refine ⟨SSet.Subcomplex.range f, inferInstance, SSet.toTop.map (SSet.Subcomplex.toRange f) t, ?_⟩
  change (SSet.toTop.map (SSet.Subcomplex.toRange f) ≫ SSet.toTop.map (SSet.Subcomplex.range
    f).ι) t = x
  rw [← Functor.map_comp]
  exact ht

/-- The genuine realization topology is final for all simplex maps. -/
theorem realization_isClosed_iff_simplex (S : Set |X|) :
    IsClosed S ↔ ∀ (n : SimplexCategory) (f : SSet.stdSimplex.obj n ⟶ X),
      IsClosed (SSet.toTop.map f ⁻¹' S) := by
  constructor
  · intro h n f
    exact h.preimage (SSet.toTop.map f).hom.continuous
  · intro h
    let e := SSet.stdSimplex.leftKanExtensionObjIsoColimit SimplexCategory.toTop X
    apply (TopCat.homeoOfIso e.symm).isClosed_preimage.mp
    apply (TopCat.isClosed_iff_of_isColimit _ (colimit.isColimit _) _).mpr
    intro j
    change IsClosed ((colimit.ι _ j ≫ e.inv) ⁻¹' S)
    rw [Functor.ι_leftKanExtensionObjIsoColimit_inv]
    exact (h j.left j.hom).preimage (SSet.toTopSimplex.inv.app j.left).hom.continuous

/-- A monotone sequence with finite range is eventually stationary. -/
theorem monotone_eventually_constant_of_finite {α : Type*} [PartialOrder α] [Finite α]
    (f : ℕ → α) (hf : Monotone f) : ∃ N, ∀ n, N ≤ n → f n = f N := by
  classical
  let index : Set.range f → ℕ := fun a ↦ a.2.choose
  obtain ⟨N, hN⟩ := (Set.finite_range index).bddAbove
  refine ⟨N, fun n hn ↦ le_antisymm ?_ (hf hn)⟩
  let a : Set.range f := ⟨f n, ⟨n, rfl⟩⟩
  have ha : f (index a) = f n := a.2.choose_spec
  exact ha ▸ hf (hN ⟨a, rfl⟩)

/-- A finite subcomplex sees only a stationary finite portion of an increasing
sequence of subcomplexes, regardless of the size of the ambient simplicial set. -/
theorem finite_subcomplex_intersection_stabilizes (A : X.Subcomplex) [SSet.Finite A]
    (B : ℕ → X.Subcomplex) (hB : Monotone B) :
    ∃ N, ∀ n, N ≤ n → A ⊓ B n = A ⊓ B N := by
  let f : ℕ → Set.Iic A := fun n ↦ ⟨A ⊓ B n, show A ⊓ B n ≤ A from inf_le_left⟩
  have hf : Monotone f := fun n m h ↦ inf_le_inf_left A (hB h)
  obtain ⟨N, hN⟩ := monotone_eventually_constant_of_finite f hf
  exact ⟨N, fun n hn ↦ congrArg Subtype.val (hN n hn)⟩

/-- A union of two genuinely finite subcomplexes is finite. -/
theorem finite_subcomplex_sup (A B : X.Subcomplex) [SSet.Finite A] [SSet.Finite B] :
    SSet.Finite (A ⊔ B : X.Subcomplex) := by
  have h : SSet.Finite (⨆ b : Bool, (if b then A else B) : X.Subcomplex) :=
    (SSet.finite_iSup_iff _).2 (fun b ↦ by
      cases b
      · simpa using (inferInstance : SSet.Finite B)
      · simpa using (inferInstance : SSet.Finite A))
  simpa only [iSup_bool_eq, Bool.false_eq_true, ite_false, ite_true, sup_comm] using h

/-- The empty subcomplex is genuinely finite. -/
instance finite_subcomplex_bot : SSet.Finite (⊥ : X.Subcomplex) where
  finite := by
    have : IsEmpty ((⊥ : X.Subcomplex) : SSet.{u}).N := ⟨fun s ↦ s.simplex.2⟩
    infer_instance

/-- Every compact subset of an actual realization lies in a genuinely
finite simplicial subcomplex. This controls the number of nondegenerate
simplices, not only their dimensions. -/
theorem realization_isCompact_subset_finiteSubcomplex {K : Set |X|} (hK : IsCompact K) :
    ∃ A : X.Subcomplex, SSet.Finite A ∧ K ⊆ realizationSubcomplexRange A := by
  classical
  by_contra h
  let FC := {A : X.Subcomplex // SSet.Finite A}
  have hchoose (A : FC) : ∃ x, x ∈ K ∧ x ∉ realizationSubcomplexRange A.1 := by
    by_contra hh
    apply h
    refine ⟨A.1, A.2, ?_⟩
    intro y hy
    by_contra hout
    exact hh ⟨y, hy, hout⟩
  let x (A : FC) : |X| := (hchoose A).choose
  have hxK (A : FC) : x A ∈ K := (hchoose A).choose_spec.1
  have hxout (A : FC) : x A ∉ realizationSubcomplexRange A.1 := (hchoose A).choose_spec.2
  have hnext (A : FC) : ∃ B : FC, A.1 ≤ B.1 ∧ x A ∈ realizationSubcomplexRange B.1 := by
    obtain ⟨B, hB, hx⟩ := realization_exists_finite_subcomplex (x A)
    let : SSet.Finite A.1 := A.2
    let : SSet.Finite B := hB
    refine ⟨⟨A.1 ⊔ B, finite_subcomplex_sup A.1 B⟩, le_sup_left, ?_⟩
    exact realizationSubcomplexRange_monotone le_sup_right hx
  let next (A : FC) : FC := (hnext A).choose
  let S : ℕ → FC := Nat.rec ⟨⊥, inferInstance⟩ (fun _ A ↦ next A)
  have hSnext (n : ℕ) : (S n).1 ≤ (S (n + 1)).1 ∧
      x (S n) ∈ realizationSubcomplexRange (S (n + 1)).1 := (hnext (S n)).choose_spec
  have hS : Monotone (fun n ↦ (S n).1) := monotone_nat_of_le_succ (fun n ↦ (hSnext n).1)
  let z (n : ℕ) : |X| := x (S n)
  have hzout (n : ℕ) : z n ∉ realizationSubcomplexRange (S n).1 := hxout (S n)
  have hzin (n : ℕ) : z n ∈ realizationSubcomplexRange (S (n + 1)).1 := (hSnext n).2
  have hfinite (A : X.Subcomplex) [SSet.Finite A] :
      (Set.range z ∩ realizationSubcomplexRange A).Finite := by
    obtain ⟨N, hN⟩ := finite_subcomplex_intersection_stabilizes A (fun n ↦ (S n).1) hS
    apply ((Set.finite_Iio N).image z).subset
    rintro y ⟨⟨n, rfl⟩, hnA⟩
    refine ⟨n, ?_, rfl⟩
    by_contra hn
    have hNn : N ≤ n := Nat.le_of_not_gt hn
    have he : A ⊓ (S (n + 1)).1 = A ⊓ (S n).1 :=
      (hN (n + 1) (hNn.trans (Nat.le_succ n))).trans (hN n hNn).symm
    have hz : z n ∈ realizationSubcomplexRange (A ⊓ (S (n + 1)).1) := by
      rw [realizationSubcomplexRange_inf]
      exact ⟨hnA, hzin n⟩
    rw [he] at hz
    exact hzout n (realizationSubcomplexRange_monotone inf_le_right hz)
  have hclosed (T : Set |X|) (hT : T ⊆ Set.range z) : IsClosed T := by
    apply (realization_isClosed_iff_simplex T).2
    intro n f
    let A := SSet.Subcomplex.range f
    have hf : (T ∩ realizationSubcomplexRange A).Finite :=
      (hfinite A).subset (Set.inter_subset_inter_left _ hT)
    have he : SSet.toTop.map f ⁻¹' T =
        SSet.toTop.map f ⁻¹' (T ∩ realizationSubcomplexRange A) := by
      ext t
      constructor
      · intro ht
        refine ⟨ht, SSet.toTop.map (SSet.Subcomplex.toRange f) t, ?_⟩
        change (SSet.toTop.map (SSet.Subcomplex.toRange f) ≫ SSet.toTop.map A.ι) t = _
        rw [← Functor.map_comp]
        rfl
      · exact fun ht ↦ ht.1
    rw [he]
    exact hf.isClosed.preimage (SSet.toTop.map f).hom.continuous
  have hrangeK : Set.range z ⊆ K := by rintro _ ⟨n, rfl⟩; exact hxK (S n)
  have hc : IsCompact (Set.range z) := by
    simpa only [Set.inter_eq_right.mpr hrangeK] using
      hK.inter_right (hclosed (Set.range z) Set.Subset.rfl)
  have hd : IsDiscrete (Set.range z) := by
    apply isDiscrete_iff_forall_mem_exists_isClosed.mpr
    intro T hT
    exact ⟨T, hclosed T hT, Set.inter_eq_left.mpr hT⟩
  have hi : Function.Injective z := by
    intro n m he
    rcases lt_trichotomy n m with hnm | hnm | hmn
    · exact False.elim (hzout m (he ▸
        realizationSubcomplexRange_monotone (hS (Nat.succ_le_of_lt hnm)) (hzin n)))
    · exact hnm
    · exact False.elim (hzout n (he.symm ▸
        realizationSubcomplexRange_monotone (hS (Nat.succ_le_of_lt hmn)) (hzin m)))
  exact (Set.infinite_range_of_injective hi) (hc.finite hd)

/-- A continuous map from a compact space factors through a genuinely finite
simplicial subcomplex, with continuous factor and exact original map. -/
theorem realization_continuousMap_factors_finiteSubcomplex
    {T : Type*} [TopologicalSpace T] [CompactSpace T] (f : C(T, |X|)) :
    ∃ A : X.Subcomplex, SSet.Finite A ∧ ∃ g : C(T, |(A : SSet.{u})|),
      (SSet.toTop.map A.ι).hom.comp g = f := by
  classical
  obtain ⟨A, hA, h⟩ := realization_isCompact_subset_finiteSubcomplex (isCompact_range f.continuous)
  have hchoose : ∀ t, ∃ a, SSet.toTop.map A.ι a = f t := fun t ↦ h ⟨t, rfl⟩
  choose g hg using hchoose
  have hcont : Continuous g := by
    apply (realization_mono_isClosedEmbedding A.ι).isInducing.continuous_iff.mpr
    have he : (SSet.toTop.map A.ι : |(A : SSet.{u})| → |X|) ∘ g = f := funext hg
    rw [he]
    exact f.continuous
  exact ⟨A, hA, ⟨g, hcont⟩, ContinuousMap.ext hg⟩

end SSet
