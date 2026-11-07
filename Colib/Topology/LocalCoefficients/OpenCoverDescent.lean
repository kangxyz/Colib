/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.SmallChainExcision
public import Colib.Topology.LocalCoefficients.SmallChainFunctoriality
public import Colib.Algebra.Homology.HomologicalComplex.BiprodQuasiIso

/-!
Adapted from `Quillen/Topology/LocalCoefficients/OpenCoverDescent.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps.

# Two-open-cover descent for actual twisted homology maps

The original spatial map between small-chain gluing sequences is constructed
on singular simplices with the target coefficients pulled back. If its two
piece maps and overlap map are quasi-isomorphisms, its combined small-chain
map is a quasi-isomorphism. For open covers of both spaces, this proves the
same assertion for the original spatial map of twisted singular chains.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits

universe u v w v' w'

namespace FundamentalGroupoid.LocalCoefficients

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  {ι : Type v} {κ : Type w} {ι' : Type v'} {κ' : Type w'}
variable (f : C(X, Y)) (U : ι → Set X) (V : κ → Set X)
  (U' : ι' → Set Y) (V' : κ' → Set Y) (A : System.{u, u} Y)
  (hU : ∀ {n : SimplexCategory} {σ : SingularSimplex X n},
    IsCoverSmall U σ → IsCoverSmall U' (f.comp σ))
  (hV : ∀ {n : SimplexCategory} {σ : SingularSimplex X n},
    IsCoverSmall V σ → IsCoverSmall V' (f.comp σ))

include hU hV in
/-- Spatial preservation of each family preserves their pairwise intersections. -/
theorem mapSmallIntersection {n : SimplexCategory} {σ : SingularSimplex X n}
    (hσ : IsCoverSmall (intersectionCover U V) σ) :
    IsCoverSmall (intersectionCover U' V') (f.comp σ) := by
  obtain ⟨hu, hv⟩ := (isCoverSmall_intersectionCover U V σ).mp hσ
  exact (isCoverSmall_intersectionCover U' V' _).mpr ⟨hU hu, hV hv⟩

include hU hV in
/-- Spatial preservation of each family preserves their combined family. -/
theorem mapSmallUnion {n : SimplexCategory} {σ : SingularSimplex X n}
    (hσ : IsCoverSmall (unionCover U V) σ) :
    IsCoverSmall (unionCover U' V') (f.comp σ) := by
  rcases (isCoverSmall_unionCover U V σ).mp hσ with hu | hv
  · exact (isCoverSmall_unionCover U' V' _).mpr (Or.inl (hU hu))
  · exact (isCoverSmall_unionCover U' V' _).mpr (Or.inr (hV hv))

/-- The map of overlap chains, with the original spatial map and coefficients. -/
def intersectionSmallPushforward :
    smallChainComplex (intersectionCover U V) (pullback f A) ⟶
      smallChainComplex (intersectionCover U' V') A :=
  smallPushforwardChainMap f _ _ A (mapSmallIntersection f U V U' V' hU hV)

/-- The map of combined small chains, with the original spatial map and coefficients. -/
def unionSmallPushforward : smallChainComplex (unionCover U V) (pullback f A) ⟶
    smallChainComplex (unionCover U' V') A :=
  smallPushforwardChainMap f _ _ A (mapSmallUnion f U V U' V' hU hV)

/-- The actual spatial map between the proved small-chain gluing sequences. -/
def smallChainGluingMap : smallChainGluingSequence U V (pullback f A) ⟶
    smallChainGluingSequence U' V' A where
  τ₁ := intersectionSmallPushforward f U V U' V' A hU hV
  τ₂ := biprod.map (smallPushforwardChainMap f U U' A hU)
    (smallPushforwardChainMap f V V' A hV)
  τ₃ := unionSmallPushforward f U V U' V' A hU hV
  comm₁₂ := by
    apply biprod.hom_ext
    · simpa [smallChainGluingSequence, smallChainGluingDifference, intersectionChainLeft,
        Category.assoc, intersectionSmallPushforward] using
        (smallPushforwardChainMap_refinement f (intersectionCover U V)
          (intersectionCover U' V') A (mapSmallIntersection f U V U' V' hU hV)
          U U' hU (fun h ↦ (isCoverSmall_intersectionCover U V _).mp h |>.1)
          (fun h ↦ (isCoverSmall_intersectionCover U' V' _).mp h |>.1)).symm
    · simpa [smallChainGluingSequence, smallChainGluingDifference, intersectionChainRight,
        Category.assoc, intersectionSmallPushforward] using
        congrArg Neg.neg (smallPushforwardChainMap_refinement f (intersectionCover U V)
          (intersectionCover U' V') A (mapSmallIntersection f U V U' V' hU hV)
          V V' hV (fun h ↦ (isCoverSmall_intersectionCover U V _).mp h |>.2)
          (fun h ↦ (isCoverSmall_intersectionCover U' V' _).mp h |>.2)).symm
  comm₂₃ := by
    apply biprod.hom_ext'
    · simpa [smallChainGluingSequence, smallChainGluingSum, unionChainLeft,
        Category.assoc, unionSmallPushforward] using
        (smallPushforwardChainMap_refinement f U U' A hU
          (unionCover U V) (unionCover U' V') (mapSmallUnion f U V U' V' hU hV)
          (fun h ↦ (isCoverSmall_unionCover U V _).mpr (Or.inl h))
          (fun h ↦ (isCoverSmall_unionCover U' V' _).mpr (Or.inl h))).symm
    · simpa [smallChainGluingSequence, smallChainGluingSum, unionChainRight,
        Category.assoc, unionSmallPushforward] using
        (smallPushforwardChainMap_refinement f V V' A hV
          (unionCover U V) (unionCover U' V') (mapSmallUnion f U V U' V' hU hV)
          (fun h ↦ (isCoverSmall_unionCover U V _).mpr (Or.inr h))
          (fun h ↦ (isCoverSmall_unionCover U' V' _).mpr (Or.inr h))).symm

/-- Two pieces and their overlap detect the original combined small-chain comparison. -/
theorem unionSmallPushforward_quasiIso
    (h₁ : QuasiIso (smallPushforwardChainMap f U U' A hU))
    (h₂ : QuasiIso (smallPushforwardChainMap f V V' A hV))
    (h₁₂ : QuasiIso (intersectionSmallPushforward f U V U' V' A hU hV)) :
    QuasiIso (unionSmallPushforward f U V U' V' A hU hV) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃
    (smallChainGluingMap f U V U' V' A hU hV)
    (smallChainGluingSequence_shortExact U V (pullback f A))
    (smallChainGluingSequence_shortExact U' V' A) h₁₂
    (HomologicalComplex.quasiIso_biprod_map _ _)

/-- Local-to-global comparison for the original spatial twisted singular map.
Both combined families must be open covers. The assumptions are the actual
maps on the two pieces and their overlap, not a presumed global comparison. -/
theorem pushforwardChainMap_quasiIso_of_open_covers
    (openU : ∀ i, IsOpen (U i)) (openV : ∀ j, IsOpen (V j))
    (coverX : ∀ x, (∃ i, x ∈ U i) ∨ (∃ j, x ∈ V j))
    (openU' : ∀ i, IsOpen (U' i)) (openV' : ∀ j, IsOpen (V' j))
    (coverY : ∀ y, (∃ i, y ∈ U' i) ∨ (∃ j, y ∈ V' j))
    (h₁ : QuasiIso (smallPushforwardChainMap f U U' A hU))
    (h₂ : QuasiIso (smallPushforwardChainMap f V V' A hV))
    (h₁₂ : QuasiIso (intersectionSmallPushforward f U V U' V' A hU hV)) :
    QuasiIso (pushforwardChainMap f A) := by
  have hsource : QuasiIso (smallChainComplexInclusion (unionCover U V) (pullback f A)) := by
    apply smallChainComplexInclusion_quasiIso
    · rintro (i | j)
      · exact openU i
      · exact openV j
    · intro x
      rcases coverX x with ⟨i, hi⟩ | ⟨j, hj⟩
      · exact ⟨Sum.inl i, hi⟩
      · exact ⟨Sum.inr j, hj⟩
  have htarget : QuasiIso (smallChainComplexInclusion (unionCover U' V') A) := by
    apply smallChainComplexInclusion_quasiIso
    · rintro (i | j)
      · exact openU' i
      · exact openV' j
    · intro y
      rcases coverY y with ⟨i, hi⟩ | ⟨j, hj⟩
      · exact ⟨Sum.inl i, hi⟩
      · exact ⟨Sum.inr j, hj⟩
  have := unionSmallPushforward_quasiIso f U V U' V' A hU hV h₁ h₂ h₁₂
  have hcomp : QuasiIso (smallChainComplexInclusion (unionCover U V) (pullback f A) ≫
      pushforwardChainMap f A) := by
    rw [← smallPushforwardChainMap_inclusion f (unionCover U V) (unionCover U' V') A
      (mapSmallUnion f U V U' V' hU hV)]
    exact inferInstanceAs (QuasiIso (unionSmallPushforward f U V U' V' A hU hV ≫ _))
  exact (quasiIso_iff_comp_left
    (smallChainComplexInclusion (unionCover U V) (pullback f A)) (pushforwardChainMap f A)).mp hcomp

end FundamentalGroupoid.LocalCoefficients
