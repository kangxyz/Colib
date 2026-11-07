/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.SmallChainGluing
public import Colib.Topology.LocalCoefficients.SmallChainQuasiIso
public import Colib.Topology.LocalCoefficients.SubspaceSmallChains
public import Mathlib.Algebra.Homology.CommSq
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels

/-!
Adapted from `Quillen/Topology/LocalCoefficients/SmallChainExcision.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual maps and pullbacks.


# Excision for genuine twisted cover-small chains

The gluing square of the actual small-chain complexes is a pushout. The
induced quotient map is therefore an isomorphism. If the combined families
form an open cover, its original map into the ambient relative twisted
chain complex is a quasi-isomorphism, by the proven small-chain comparison
and the long exact sequences of actual cokernel complexes.
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
variable (U : ι → Set X) (V : κ → Set X) (A : System.{u, u} X)

/-- The actual gluing square is a pushout of twisted chain complexes. -/
theorem smallChainGluing_isPushout :
    IsPushout (intersectionChainLeft U V A) (intersectionChainRight U V A)
      (unionChainLeft U V A) (unionChainRight U V A) := by
  let sq : CommSq (intersectionChainLeft U V A) (intersectionChainRight U V A)
      (unionChainLeft U V A) (unionChainRight U V A) :=
    ⟨intersection_union_square U V A⟩
  refine ⟨sq, ⟨sq.isColimitEquivIsColimitCokernelCofork.symm ?_⟩⟩
  exact (smallChainGluingSequence_shortExact U V A).gIsCokernel

/-- The original quotient map across the small-chain gluing square. -/
def smallChainQuotientMap : cokernel (intersectionChainLeft U V A) ⟶
    cokernel (unionChainRight U V A) :=
  cokernel.map _ _ (intersectionChainRight U V A) (unionChainLeft U V A)
    (intersection_union_square U V A)

/-- The quotient gluing map is an actual isomorphism of twisted complexes. -/
instance smallChainQuotientMap_isIso : IsIso (smallChainQuotientMap U V A) :=
  isIso_cokernel_map_of_isPushout (smallChainGluing_isPushout U V A)

@[reassoc (attr := simp)]
theorem unionChainLeft_inclusion :
    unionChainLeft U V A ≫ smallChainComplexInclusion (unionCover U V) A =
      smallChainComplexInclusion U A :=
  smallChainRefinement_inclusion U (unionCover U V) A
    (fun h ↦ (isCoverSmall_unionCover U V _).mpr (Or.inl h))

@[reassoc (attr := simp)]
theorem unionChainRight_inclusion :
    unionChainRight U V A ≫ smallChainComplexInclusion (unionCover U V) A =
      smallChainComplexInclusion V A :=
  smallChainRefinement_inclusion V (unionCover U V) A
    (fun h ↦ (isCoverSmall_unionCover U V _).mpr (Or.inr h))

@[reassoc (attr := simp)]
theorem intersectionChainLeft_inclusion :
    intersectionChainLeft U V A ≫ smallChainComplexInclusion U A =
      intersectionChainRight U V A ≫ smallChainComplexInclusion V A := by
  unfold intersectionChainLeft intersectionChainRight
  exact (smallChainRefinement_inclusion (intersectionCover U V) U A
    (fun h ↦ (isCoverSmall_intersectionCover U V _).mp h |>.1)).trans
    (smallChainRefinement_inclusion (intersectionCover U V) V A
      (fun h ↦ (isCoverSmall_intersectionCover U V _).mp h |>.2)).symm

/-- The ambient relative complex uses the original inclusion of small chains. -/
def relativeSmallChainComplex (V : κ → Set X) (A : System.{u, u} X) :
    ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  cokernel (smallChainComplexInclusion V A)

/-- The original chain map in excision, retaining every spatial inclusion. -/
def smallChainExcisionMap : cokernel (intersectionChainLeft U V A) ⟶
    relativeSmallChainComplex V A :=
  cokernel.map _ _ (intersectionChainRight U V A) (smallChainComplexInclusion U A)
    (intersectionChainLeft_inclusion U V A)

/-- The quotient comparison from combined small chains to all ambient chains. -/
def relativeSmallChainComparison : cokernel (unionChainRight U V A) ⟶
    relativeSmallChainComplex V A :=
  cokernel.map _ _ (𝟙 _) (smallChainComplexInclusion (unionCover U V) A)
    (by simp only [unionChainRight_inclusion, Category.id_comp])

/-- Factoring the original excision map through the actual quotient isomorphism. -/
@[reassoc]
theorem smallChainExcisionMap_factor :
    smallChainQuotientMap U V A ≫ relativeSmallChainComparison U V A =
      smallChainExcisionMap U V A := by
  apply (cancel_epi (cokernel.π (intersectionChainLeft U V A))).mp
  simp only [smallChainQuotientMap, relativeSmallChainComparison, smallChainExcisionMap,
    cokernel.map, cokernel.π_desc_assoc, cokernel.π_desc, Category.assoc]
  rw [← Category.assoc, unionChainLeft_inclusion]


/-- For an open cover, the relative comparison is a quasi-isomorphism on the
actual cokernel complexes, rather than an assumed excision principle. -/
theorem relativeSmallChainComparison_quasiIso
    (hU : ∀ i, IsOpen (U i)) (hV : ∀ j, IsOpen (V j))
    (hcover : ∀ x, (∃ i, x ∈ U i) ∨ (∃ j, x ∈ V j)) :
    QuasiIso (relativeSmallChainComparison U V A) := by
  have : Mono (unionChainRight U V A) := smallChainRefinement_mono V (unionCover U V) A
    (fun h ↦ (isCoverSmall_unionCover U V _).mpr (Or.inr h))
  let S : ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
    ShortComplex.mk (unionChainRight U V A) (cokernel.π _) (cokernel.condition _)
  let T : ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
    ShortComplex.mk (smallChainComplexInclusion V A) (cokernel.π _) (cokernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  have hT : T.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  let φ : S ⟶ T :=
    { τ₁ := 𝟙 _
      τ₂ := smallChainComplexInclusion (unionCover U V) A
      τ₃ := relativeSmallChainComparison U V A
      comm₁₂ := by simp [S, T]
      comm₂₃ := by simp [S, T, relativeSmallChainComparison] }
  apply HomologicalComplex.HomologySequence.quasiIso_τ₃ φ hS hT
  · change QuasiIso (𝟙 (smallChainComplex V A))
    infer_instance
  · apply smallChainComplexInclusion_quasiIso
    · rintro (i | j)
      · exact hU i
      · exact hV j
    · intro x
      rcases hcover x with ⟨i, hi⟩ | ⟨j, hj⟩
      · exact ⟨Sum.inl i, hi⟩
      · exact ⟨Sum.inr j, hj⟩

/-- Genuine twisted excision for two families forming an open cover. -/
theorem smallChainExcisionMap_quasiIso
    (hU : ∀ i, IsOpen (U i)) (hV : ∀ j, IsOpen (V j))
    (hcover : ∀ x, (∃ i, x ∈ U i) ∨ (∃ j, x ∈ V j)) :
    QuasiIso (smallChainExcisionMap U V A) := by
  have := relativeSmallChainComparison_quasiIso U V A hU hV hcover
  rw [← smallChainExcisionMap_factor U V A]
  infer_instance

/-- One-set relative small chains are exactly the relative singular chain complex. -/
def relativeSingularSmallChainIso (W : Set X) (A : System.{u, u} X) :
    relativeSingularChainComplex W A ≅ relativeSmallChainComplex (singletonCover W) A := by
  let f : relativeSingularChainComplex W A ⟶
      relativeSmallChainComplex (singletonCover W) A :=
    cokernel.map _ _ (subspaceSmallChainIso W A).hom (𝟙 _)
      (by simpa only [Category.comp_id] using (subspaceSmallChainIso_hom_inclusion W A).symm)
  have : IsIso f := by dsimp [f]; infer_instance
  exact asIso f

/-- Quotient excision induces isomorphisms on actual homology in every degree. -/
theorem smallChainExcisionMap_homology_isIso
    (hU : ∀ i, IsOpen (U i)) (hV : ∀ j, IsOpen (V j))
    (hcover : ∀ x, (∃ i, x ∈ U i) ∨ (∃ j, x ∈ V j)) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (smallChainExcisionMap U V A) n) := by
  have := smallChainExcisionMap_quasiIso U V A hU hV hcover
  infer_instance

/-- Two-open-set excision, into the actual relative singular chain complex.
The source is the quotient of chains in `U` by chains in `U ∩ V`, with their
original ambient coefficient fibers, as identified by `subspaceSmallChainIso`. -/
def openExcisionChainMap (U V : Set X) (A : System.{u, u} X) :
    cokernel (intersectionChainLeft (singletonCover U) (singletonCover V) A) ⟶
      relativeSingularChainComplex V A :=
  smallChainExcisionMap (singletonCover U) (singletonCover V) A ≫
    (relativeSingularSmallChainIso V A).inv

/-- Two open subsets covering the space satisfy actual twisted relative excision. -/
theorem openExcisionChainMap_quasiIso (U V : Set X) (A : System.{u, u} X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    QuasiIso (openExcisionChainMap U V A) := by
  have := smallChainExcisionMap_quasiIso (singletonCover U) (singletonCover V) A
    (fun _ ↦ hU) (fun _ ↦ hV) (fun x ↦ by
      have hx : x ∈ U ∪ V := by rw [hcover]; trivial
      rcases hx with hx | hx
      · exact Or.inl ⟨(), hx⟩
      · exact Or.inr ⟨(), hx⟩)
  unfold openExcisionChainMap
  infer_instance

/-- Every degree of genuine local-coefficient relative homology obeys open excision. -/
theorem openExcisionChainMap_homology_isIso (U V : Set X) (A : System.{u, u} X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (openExcisionChainMap U V A) n) := by
  have := openExcisionChainMap_quasiIso U V A hU hV hcover
  infer_instance

end FundamentalGroupoid.LocalCoefficients
