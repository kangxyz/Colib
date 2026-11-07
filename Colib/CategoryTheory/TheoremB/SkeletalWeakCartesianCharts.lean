/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyPullback.WeakCalculus
public import Colib.CategoryTheory.TheoremB.SkeletalCartesianInduction
public import Colib.CategoryTheory.TheoremB.SkeletalCartesianCoordinates
public import Colib.CategoryTheory.TheoremB.SkeletalCartesianStageCube

/-!
# Original characteristic squares for arbitrary coefficient transformations

Both coefficient diagrams are retained. The maps are the original realized
characteristic charts and restriction inclusions, with their naturality squares.


Implementation provenance:
`Quillen/CategoryTheory/TheoremB/SkeletalWeakCartesianCharts.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.TheoremA


noncomputable section
open Topology TopCat SSet Topology.HomotopyPullback
open CategoryTheory Limits Opposite
open scoped Simplicial Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.TheoremB.Skeletal
open TheoremA
variable {D : Type u} [SmallCategory D] {H J : D ⥤ SSet.{u}} (η : H ⟶ J)

/-- The actual realized transformation on a base restriction. -/
abbrev realizedRestrictionTransformation (A : (nerve D).Subcomplex) :=
  realizationFunctor.map (replacementRestrictionMap η A)

/-- Naturality of the original realized characteristic charts. -/
theorem realizedSimplexChart_coefficient_square (A : (nerve D).Subcomplex) {n : ℕ}
    (s : (nerve D).obj (op ⦋n⦌)) (hs : s ∈ A.obj (op ⦋n⦌)) :
    realizationFunctor.map (simplexChart H A s hs) ≫ realizedRestrictionTransformation η A =
      realizationFunctor.map (outerProductCoefficientMap (K := Δ[n]) (η.app (s.obj 0))) ≫
        realizationFunctor.map (simplexChart J A s hs) := by
  rw [← realizationFunctor.map_comp, ← realizationFunctor.map_comp,
    simplexChart_coefficient]

/-- Complete weakness of the unchanged characteristic comparison for η. -/
def ChartWeakCartesian (A : (nerve D).Subcomplex) {n : ℕ}
    (s : (nerve D).obj (op ⦋n⦌)) (hs : s ∈ A.obj (op ⦋n⦌)) : Prop :=
  WeakCartesian
    (realizationFunctor.map (outerProductCoefficientMap (K := Δ[n]) (η.app (s.obj 0)))).hom
    (realizedRestrictionTransformation η A).hom
    (realizationFunctor.map (simplexChart H A s hs)).hom
    (realizationFunctor.map (simplexChart J A s hs)).hom
    (congrArg TopCat.Hom.hom (realizedSimplexChart_coefficient_square η A s hs))

/-- Naturality of actual restriction inclusions. -/
theorem realizedRestriction_coefficient_square {A B : (nerve D).Subcomplex} (h : A ≤ B) :
    realizationFunctor.map (replacementRestrictionInclusion H h) ≫
        realizedRestrictionTransformation η B =
      realizedRestrictionTransformation η A ≫
        realizationFunctor.map (replacementRestrictionInclusion J h) := by
  rw [← realizationFunctor.map_comp, ← realizationFunctor.map_comp]
  rfl

/-- The original restriction comparison for an arbitrary transformation. -/
def RestrictionWeakCartesian {A B : (nerve D).Subcomplex} (h : A ≤ B) : Prop :=
  WeakCartesian (realizedRestrictionTransformation η A).hom
    (realizedRestrictionTransformation η B).hom
    (realizationFunctor.map (replacementRestrictionInclusion H h)).hom
    (realizationFunctor.map (replacementRestrictionInclusion J h)).hom
    (congrArg TopCat.Hom.hom (realizedRestriction_coefficient_square η h))

/-- Original charts propagate along weak-cartesian restriction inclusions. -/
theorem ChartWeakCartesian.enlarge {A B : (nerve D).Subcomplex} (h : A ≤ B)
    {n : ℕ} (s : (nerve D).obj (op ⦋n⦌)) (hs : s ∈ A.obj (op ⦋n⦌))
    (hc : ChartWeakCartesian η A s hs) (hi : RestrictionWeakCartesian η h) :
    ChartWeakCartesian η B s (h _ hs) := by
  have hh := hc.paste hi
  have hf : realizationFunctor.map (simplexChart H A s hs) ≫
      realizationFunctor.map (replacementRestrictionInclusion H h) =
      realizationFunctor.map (simplexChart H B s (h _ hs)) := by
    rw [← realizationFunctor.map_comp, simplexChart_inclusion]
  have hg : realizationFunctor.map (simplexChart J A s hs) ≫
      realizationFunctor.map (replacementRestrictionInclusion J h) =
      realizationFunctor.map (simplexChart J B s (h _ hs)) := by
    rw [← realizationFunctor.map_comp, simplexChart_inclusion]
  exact hh.congr rfl rfl (congrArg TopCat.Hom.hom hf) (congrArg TopCat.Hom.hom hg)

/-- Restriction comparisons compose with their original full path. -/
theorem RestrictionWeakCartesian.trans {A B C : (nerve D).Subcomplex}
    {h : A ≤ B} {h' : B ≤ C} (hc : RestrictionWeakCartesian η h)
    (hc' : RestrictionWeakCartesian η h') : RestrictionWeakCartesian η (h.trans h') := by
  have hh := hc.paste hc'
  apply hh.congr rfl rfl
  · change (realizationFunctor.map _ ≫ realizationFunctor.map _).hom = _
    rw [← realizationFunctor.map_comp]
    rfl
  · change (realizationFunctor.map _ ≫ realizationFunctor.map _).hom = _
    rw [← realizationFunctor.map_comp]
    rfl

/-- Identity restriction squares have their original canonical comparison. -/
theorem RestrictionWeakCartesian.refl (A : (nerve D).Subcomplex) :
    RestrictionWeakCartesian η (le_refl A) := by
  change WeakCartesian (realizedRestrictionTransformation η A).hom
    (realizedRestrictionTransformation η A).hom
    (realizationFunctor.map (𝟙 _)).hom (realizationFunctor.map (𝟙 _)).hom _
  exact (cartesianIdentity (realizedRestrictionTransformation η A).hom).weak.congr
    rfl rfl (by simp) (by simp)

/-- The sequential stage comparison is literally the same restriction comparison. -/
theorem stageWeakCartesian_of_restrictionWeakCartesian (k n : ℕ) (h : k ≤ n)
    (hc : RestrictionWeakCartesian η ((nerve D).skeleton.monotone h)) :
    IsWeakHomotopyEquivalence
      (Topology.HomotopyPullback.Sequential.stageComparison
        (realizedReplacementSkeletonMap η) k n h) := hc

/-- Restricted characteristic charts also preserve the original coefficients. -/
theorem restrictedSimplexChart_coefficient (A : (nerve D).Subcomplex) {n : ℕ}
    (s : (nerve D).obj (op ⦋n⦌)) (K : (Δ[n] : SSet.{u}).Subcomplex)
    (hs : ∀ (p : SimplexCategoryᵒᵖ) (a : K.obj p),
      (nerve D).map a.1.down.op s ∈ A.obj p) :
    restrictedSimplexChart H A s K hs ≫ replacementRestrictionMap η A =
      outerProductCoefficientMap (η.app (s.obj 0)) ≫ restrictedSimplexChart J A s K hs := by
  ext p q x : 5
  apply congrArg (Sigma.mk _)
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (η.naturality (firstVertexEdge x.1.1.down.op s)) q) x.2

/-- The precise realized square on every restricted characteristic chart. -/
theorem realizedRestrictedSimplexChart_coefficient_square (A : (nerve D).Subcomplex) {n : ℕ}
    (s : (nerve D).obj (op ⦋n⦌)) (K : (Δ[n] : SSet.{u}).Subcomplex)
    (hs : ∀ (p : SimplexCategoryᵒᵖ) (a : K.obj p),
      (nerve D).map a.1.down.op s ∈ A.obj p) :
    realizationFunctor.map (restrictedSimplexChart H A s K hs) ≫
        realizedRestrictionTransformation η A =
      realizationFunctor.map (outerProductCoefficientMap (K := K) (η.app (s.obj 0))) ≫
        realizationFunctor.map (restrictedSimplexChart J A s K hs) := by
  rw [← realizationFunctor.map_comp, ← realizationFunctor.map_comp,
    restrictedSimplexChart_coefficient]

/-- The transition hypothesis is the original η naturality comparison. -/
def TransitionWeakCartesian : Prop :=
  ∀ ⦃d e : D⦄ (f : d ⟶ e),
    WeakCartesian (SSet.toTop.map (η.app d)).hom (SSet.toTop.map (η.app e)).hom
      (SSet.toTop.map (H.map f)).hom (SSet.toTop.map (J.map f)).hom
      (congrArg TopCat.Hom.hom (show SSet.toTop.map (H.map f) ≫ SSet.toTop.map (η.app e) =
        SSet.toTop.map (η.app d) ≫ SSet.toTop.map (J.map f) from by
        rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp, η.naturality f]))

end CategoryTheory.TheoremB.Skeletal
