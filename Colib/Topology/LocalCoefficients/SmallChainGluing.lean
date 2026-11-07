/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.SmallChainRefinement
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
Adapted from `Quillen/Topology/LocalCoefficients/SmallChainGluing.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps and signs.

# Gluing genuine twisted small chains

For two families of subsets, the chains small in both families map by the
difference of their inclusions into the direct sum of the two small-chain
complexes. The sum of the inclusions maps onto the chains small in either
family. This sequence is genuinely short exact, with explicit degreewise
splittings on the original singular-simplex summands. No coefficient system
is trivialized and no exactness hypothesis is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits
open scoped Simplicial

universe u v w

namespace FundamentalGroupoid.LocalCoefficients

variable {X : Type u} [TopologicalSpace X] {ι : Type v} {κ : Type w}

/-- The family containing every member of either input family. -/
def unionCover (U : ι → Set X) (V : κ → Set X) : ι ⊕ κ → Set X := Sum.elim U V

/-- The family of pairwise intersections. -/
def intersectionCover (U : ι → Set X) (V : κ → Set X) : ι × κ → Set X :=
  fun p ↦ U p.1 ∩ V p.2

@[simp]
theorem isCoverSmall_unionCover (U : ι → Set X) (V : κ → Set X)
    {n : SimplexCategory} (σ : SingularSimplex X n) :
    IsCoverSmall (unionCover U V) σ ↔ IsCoverSmall U σ ∨ IsCoverSmall V σ := by
  constructor
  · rintro ⟨i | j, h⟩
    · exact Or.inl ⟨i, h⟩
    · exact Or.inr ⟨j, h⟩
  · rintro (⟨i, h⟩ | ⟨j, h⟩)
    · exact ⟨Sum.inl i, h⟩
    · exact ⟨Sum.inr j, h⟩

@[simp]
theorem isCoverSmall_intersectionCover (U : ι → Set X) (V : κ → Set X)
    {n : SimplexCategory} (σ : SingularSimplex X n) :
    IsCoverSmall (intersectionCover U V) σ ↔ IsCoverSmall U σ ∧ IsCoverSmall V σ := by
  constructor
  · rintro ⟨⟨i, j⟩, h⟩
    exact ⟨⟨i, fun x hx ↦ (h hx).1⟩, ⟨j, fun x hx ↦ (h hx).2⟩⟩
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    exact ⟨⟨i, j⟩, fun x hx ↦ ⟨hi hx, hj hx⟩⟩

variable (U : ι → Set X) (V : κ → Set X) (A : System.{u, u} X)

/-- The genuine inclusion of intersection-small chains into the first complex. -/
def intersectionChainLeft :
    smallChainComplex (intersectionCover U V) A ⟶ smallChainComplex U A :=
  smallChainRefinement _ _ A (fun h ↦ (isCoverSmall_intersectionCover U V _).mp h |>.1)

/-- The genuine inclusion of intersection-small chains into the second complex. -/
def intersectionChainRight :
    smallChainComplex (intersectionCover U V) A ⟶ smallChainComplex V A :=
  smallChainRefinement _ _ A (fun h ↦ (isCoverSmall_intersectionCover U V _).mp h |>.2)

/-- The first original small-chain inclusion into the combined family. -/
def unionChainLeft : smallChainComplex U A ⟶ smallChainComplex (unionCover U V) A :=
  smallChainRefinement _ _ A (fun h ↦ (isCoverSmall_unionCover U V _).mpr (Or.inl h))

/-- The second original small-chain inclusion into the combined family. -/
def unionChainRight : smallChainComplex V A ⟶ smallChainComplex (unionCover U V) A :=
  smallChainRefinement _ _ A (fun h ↦ (isCoverSmall_unionCover U V _).mpr (Or.inr h))

@[reassoc]
theorem intersection_union_square :
    intersectionChainLeft U V A ≫ unionChainLeft U V A =
      intersectionChainRight U V A ≫ unionChainRight U V A := by
  ext n : 1
  apply Sigma.hom_ext
  intro σ
  change smallChainInclusion (intersectionCover U V) A σ ≫ _ =
    smallChainInclusion (intersectionCover U V) A σ ≫ _
  simp [intersectionChainLeft, intersectionChainRight, unionChainLeft, unionChainRight,
    smallChainRefinement, smallSimplicialRefinement, smallModuleRefinement,
    smallChainInclusion]


/-- Difference of the two actual intersection inclusions. -/
def smallChainGluingDifference : smallChainComplex (intersectionCover U V) A ⟶
    smallChainComplex U A ⊞ smallChainComplex V A :=
  biprod.lift (intersectionChainLeft U V A) (-intersectionChainRight U V A)

/-- Sum of the actual inclusions into the combined family. -/
def smallChainGluingSum : smallChainComplex U A ⊞ smallChainComplex V A ⟶
    smallChainComplex (unionCover U V) A :=
  biprod.desc (unionChainLeft U V A) (unionChainRight U V A)

@[reassoc (attr := simp)]
theorem smallChainGluingDifference_sum :
    smallChainGluingDifference U V A ≫ smallChainGluingSum U V A = 0 := by
  simp [smallChainGluingDifference, smallChainGluingSum, biprod.lift_desc,
    intersection_union_square]

/-- The original small-chain gluing sequence, before proving exactness. -/
def smallChainGluingSequence : ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
  ShortComplex.mk (smallChainGluingDifference U V A) (smallChainGluingSum U V A)
    (smallChainGluingDifference_sum U V A)

/-- Degreewise projection to the intersection, using the second component.
This auxiliary splitting is not claimed to commute with the differential. -/
def smallChainGluingRetraction (n : ℕ) :
    (smallChainComplex U A ⊞ smallChainComplex V A).X n ⟶
      (smallChainComplex (intersectionCover U V) A).X n :=
  -(biprod.snd : smallChainComplex U A ⊞ smallChainComplex V A ⟶
    smallChainComplex V A).f n ≫ smallModuleInclusion V A ⦋n⦌ ≫
      smallModuleProjection (intersectionCover U V) A ⦋n⦌

/-- Choose the first summand when a simplex is small in both families.
This is only a degreewise section, as required for short exactness. -/
def smallChainGluingSection (n : ℕ) :
    (smallChainComplex (unionCover U V) A).X n ⟶
      (smallChainComplex U A ⊞ smallChainComplex V A).X n := by
  classical
  exact Sigma.desc fun σ ↦ if h : IsCoverSmall U σ.val then
    smallChainInclusion U A ⟨σ.val, h⟩ ≫
      (biprod.inl : smallChainComplex U A ⟶ _).f n
    else smallChainInclusion V A
      ⟨σ.val, ((isCoverSmall_unionCover U V σ.val).mp σ.property).resolve_left h⟩ ≫
        (biprod.inr : smallChainComplex V A ⟶ _).f n

/-- The difference inclusion has the stated degreewise retraction. -/
@[reassoc]
theorem smallChainGluingDifference_retraction (n : ℕ) :
    (smallChainGluingDifference U V A).f n ≫ smallChainGluingRetraction U V A n = 𝟙 _ := by
  classical
  apply Sigma.hom_ext
  intro σ
  change smallChainInclusion (intersectionCover U V) A σ ≫ _ =
    smallChainInclusion (intersectionCover U V) A σ
  have hσ := (isCoverSmall_intersectionCover U V σ.val).mp σ.property
  simp [smallChainGluingDifference, smallChainGluingRetraction,
    ← Category.assoc, HomologicalComplex.biprod_lift_snd_f,
    intersectionChainRight, smallChainRefinement, smallSimplicialRefinement,
    smallModuleRefinement, smallChainInclusion, smallModuleInclusion,
    smallModuleProjection, chainInclusion, hσ]

/-- The sum inclusion has the stated degreewise section. -/
@[reassoc]
theorem smallChainGluingSection_sum (n : ℕ) :
    smallChainGluingSection U V A n ≫ (smallChainGluingSum U V A).f n = 𝟙 _ := by
  classical
  apply Sigma.hom_ext
  intro σ
  change smallChainInclusion (unionCover U V) A σ ≫ _ =
    smallChainInclusion (unionCover U V) A σ
  by_cases h : IsCoverSmall U σ.val
  all_goals
    simp [smallChainGluingSection, smallChainGluingSum, smallChainInclusion, h,
      unionChainLeft, unionChainRight, smallChainRefinement, smallSimplicialRefinement,
      smallModuleRefinement]

/-- The two degreewise splittings add to the original identity. -/
theorem smallChainGluing_splitting_identity (n : ℕ) :
    smallChainGluingRetraction U V A n ≫ (smallChainGluingDifference U V A).f n +
      (smallChainGluingSum U V A).f n ≫ smallChainGluingSection U V A n = 𝟙 _ := by
  classical
  apply HomologicalComplex.biprodX_ext_from
  · apply Sigma.hom_ext
    intro σ
    change smallChainInclusion U A σ ≫ _ = smallChainInclusion U A σ ≫ _
    simp [smallChainGluingRetraction, smallChainGluingSum, smallChainGluingSection,
      Preadditive.comp_add, unionChainLeft, smallChainRefinement,
      smallSimplicialRefinement, smallModuleRefinement, smallChainInclusion, σ.property]
  · apply Sigma.hom_ext
    intro σ
    change smallChainInclusion V A σ ≫ _ = smallChainInclusion V A σ ≫ _
    apply HomologicalComplex.biprodX_ext_to <;> by_cases h : IsCoverSmall U σ.val
    all_goals
      simp [smallChainGluingRetraction, smallChainGluingSum, smallChainGluingSection,
        Preadditive.comp_add, unionChainRight, smallChainRefinement,
        smallSimplicialRefinement, smallModuleRefinement, smallChainInclusion,
        smallModuleInclusion, smallModuleProjection, chainInclusion,
        isCoverSmall_intersectionCover, h, σ.property, smallChainGluingDifference,
        intersectionChainLeft, intersectionChainRight, smallChainComplex, smallSimplicialModule]

/-- Actual twisted small chains satisfy a degreewise split short exact gluing sequence. -/
theorem smallChainGluingSequence_shortExact : (smallChainGluingSequence U V A).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact (show ((smallChainGluingSequence U V A).map
    (HomologicalComplex.eval _ _ n)).Splitting from
    { r := smallChainGluingRetraction U V A n
      s := smallChainGluingSection U V A n
      f_r := smallChainGluingDifference_retraction U V A n
      s_g := smallChainGluingSection_sum U V A n
      id := smallChainGluing_splitting_identity U V A n }).shortExact

end FundamentalGroupoid.LocalCoefficients
