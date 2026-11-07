/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.SmallChains
public import Colib.Topology.LocalCoefficients.BarycentricHomotopy
public import Colib.Algebra.Homology.ChainComplex.DegreeRaisingHomotopy

/-!
Adapted from `Quillen/Topology/LocalCoefficients/SmallSubdivision.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps and signs.

# Barycentric subdivision and its homotopy on cover-small chains

Every affine term of both actual operators factors through its original singular
simplex. Consequently the original small-chain subcomplex is preserved by both
operators, with the original local coefficient transport unchanged.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open FreeAbelianGroup stdSimplex
open CategoryTheory Limits
open scoped Simplicial

universe u v

namespace FundamentalGroupoid.LocalCoefficients

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- A small summand is fixed by the degreewise projection and inclusion. -/
@[reassoc]
theorem chainInclusion_smallProjection_inclusion (U : ι → Set X)
    (A : System.{u, u} X) {n : ℕ} (σ : SingularSimplex X ⦋n⦌)
    (hσ : IsCoverSmall U σ) :
    chainInclusion A σ ≫ smallModuleProjection U A ⦋n⦌ ≫
      smallModuleInclusion U A ⦋n⦌ = chainInclusion A σ := by
  simp [smallModuleProjection, chainInclusion, hσ]

/-- Transport within a small simplex still lands in an actual small summand. -/
@[reassoc]
theorem transportedSimplexTerm_smallProjection_inclusion (U : ι → Set X)
    (A : System.{u, u} X) {N n : ℕ} (σ : SingularSimplex X ⦋N⦌)
    (hσ : IsCoverSmall U σ) (x : _root_.stdSimplex ℝ (Fin (N + 1)))
    (f : C(_root_.stdSimplex ℝ (Fin (n + 1)), _root_.stdSimplex ℝ (Fin (N + 1)))) :
    transportedSimplexTerm A σ x f ≫ smallModuleProjection U A ⦋n⦌ ≫
      smallModuleInclusion U A ⦋n⦌ = transportedSimplexTerm A σ x f := by
  rw [transportedSimplexTerm, Category.assoc,
    chainInclusion_smallProjection_inclusion U A _ (hσ.precomp f)]

/-- Each checked affine term preserves cover-smallness. -/
@[reassoc]
theorem affineListTerm_smallProjection_inclusion (U : ι → Set X)
    (A : System.{u, u} X) {N : ℕ} (σ : SingularSimplex X ⦋N⦌)
    (hσ : IsCoverSmall U σ) (x : _root_.stdSimplex ℝ (Fin (N + 1))) (n : ℕ)
    (l : List (_root_.stdSimplex ℝ (Fin (N + 1)))) :
    affineListTerm A σ x n l ≫ smallModuleProjection U A ⦋n⦌ ≫
      smallModuleInclusion U A ⦋n⦌ = affineListTerm A σ x n l := by
  unfold affineListTerm
  split_ifs with hl
  · exact transportedSimplexTerm_smallProjection_inclusion U A σ hσ x _
  · simp

/-- Any finite affine-list chain inside a small original simplex is small. -/
@[reassoc]
theorem realizeListChain_smallProjection_inclusion (U : ι → Set X)
    (A : System.{u, u} X) {N : ℕ} (σ : SingularSimplex X ⦋N⦌)
    (hσ : IsCoverSmall U σ) (x : _root_.stdSimplex ℝ (Fin (N + 1))) (n : ℕ)
    (c : OrientedList.Chain (_root_.stdSimplex ℝ (Fin (N + 1)))) :
    realizeListChain A σ x n c ≫ smallModuleProjection U A ⦋n⦌ ≫
      smallModuleInclusion U A ⦋n⦌ = realizeListChain A σ x n c := by
  induction c using FreeAbelianGroup.induction_on with
  | zero => simp
  | of l =>
    rw [realizeListChain_generator]
    exact affineListTerm_smallProjection_inclusion U A σ hσ x n l
  | neg c hc => simp only [map_neg, Preadditive.neg_comp, hc]
  | add c d hc hd => simp only [map_add, Preadditive.add_comp, hc, hd]

/-- The actual subdivision restricted to the actual small modules. -/
def smallBarycentricSubdivisionMap (U : ι → Set X) (A : System.{u, u} X) (n : ℕ) :
    (smallChainComplex U A).X n ⟶ (smallChainComplex U A).X n :=
  smallModuleInclusion U A ⦋n⦌ ≫ barycentricSubdivisionMap A n ≫
    smallModuleProjection U A ⦋n⦌

/-- Restricting subdivision retains exactly the original twisted operator. -/
@[reassoc (attr := simp)]
theorem smallBarycentricSubdivisionMap_inclusion (U : ι → Set X)
    (A : System.{u, u} X) (n : ℕ) :
    smallBarycentricSubdivisionMap U A n ≫ smallModuleInclusion U A ⦋n⦌ =
      smallModuleInclusion U A ⦋n⦌ ≫ barycentricSubdivisionMap A n := by
  apply Sigma.hom_ext
  intro σ
  change smallChainInclusion U A σ ≫ _ = smallChainInclusion U A σ ≫ _
  simp only [smallBarycentricSubdivisionMap, Category.assoc,
    smallChainInclusion_smallModuleInclusion_assoc,
    chainInclusion_barycentricSubdivisionMap_assoc,
    chainInclusion_barycentricSubdivisionMap]
  exact realizeListChain_smallProjection_inclusion U A σ.val σ.property _ _ _

/-- The restricted actual subdivision commutes with the small differential. -/
@[reassoc]
theorem smallBarycentricSubdivisionMap_d (U : ι → Set X)
    (A : System.{u, u} X) (n : ℕ) :
    smallBarycentricSubdivisionMap U A (n + 1) ≫ (smallChainComplex U A).d (n + 1) n =
      (smallChainComplex U A).d (n + 1) n ≫ smallBarycentricSubdivisionMap U A n := by
  apply (cancel_mono (smallModuleInclusion U A ⦋n⦌)).mp
  have comm := ((smallChainComplexInclusion U A).comm (n + 1) n).symm
  change (smallChainComplex U A).d (n + 1) n ≫ smallModuleInclusion U A ⦋n⦌ =
    smallModuleInclusion U A ⦋n + 1⦌ ≫ (singularChainComplex A).d (n + 1) n at comm
  simp only [Category.assoc, comm, smallBarycentricSubdivisionMap_inclusion_assoc,
    smallBarycentricSubdivisionMap_inclusion]
  rw [barycentricSubdivisionMap_d, ← Category.assoc, ← Category.assoc, comm]

/-- The genuine barycentric chain endomorphism on cover-small chains. -/
def smallBarycentricSubdivision (U : ι → Set X) (A : System.{u, u} X) :
    smallChainComplex U A ⟶ smallChainComplex U A :=
  ChainComplex.ofHom (smallBarycentricSubdivisionMap U A)
    (smallBarycentricSubdivisionMap_d U A)

@[simp]
theorem smallBarycentricSubdivision_f (U : ι → Set X) (A : System.{u, u} X) (n : ℕ) :
    (smallBarycentricSubdivision U A).f n = smallBarycentricSubdivisionMap U A n := rfl

/-- Inclusion intertwines the two constructed subdivision chain maps. -/
@[reassoc (attr := simp)]
theorem smallBarycentricSubdivision_inclusion (U : ι → Set X) (A : System.{u, u} X) :
    smallBarycentricSubdivision U A ≫ smallChainComplexInclusion U A =
      smallChainComplexInclusion U A ≫ barycentricSubdivision A := by
  ext n : 1
  exact smallBarycentricSubdivisionMap_inclusion U A n

/-- The original coning homotopy restricted degreewise to small chains. -/
def smallBarycentricHomotopyMap (U : ι → Set X) (A : System.{u, u} X) (n : ℕ) :
    (smallChainComplex U A).X n ⟶ (smallChainComplex U A).X (n + 1) :=
  smallModuleInclusion U A ⦋n⦌ ≫ barycentricHomotopyMap A n ≫
    smallModuleProjection U A ⦋n + 1⦌

/-- Restriction of the homotopy also retains the genuine original operator. -/
@[reassoc (attr := simp)]
theorem smallBarycentricHomotopyMap_inclusion (U : ι → Set X)
    (A : System.{u, u} X) (n : ℕ) :
    smallBarycentricHomotopyMap U A n ≫ smallModuleInclusion U A ⦋n + 1⦌ =
      smallModuleInclusion U A ⦋n⦌ ≫ barycentricHomotopyMap A n := by
  apply Sigma.hom_ext
  intro σ
  change smallChainInclusion U A σ ≫ _ = smallChainInclusion U A σ ≫ _
  simp only [smallBarycentricHomotopyMap, Category.assoc,
    smallChainInclusion_smallModuleInclusion_assoc,
    chainInclusion_barycentricHomotopyMap_assoc,
    chainInclusion_barycentricHomotopyMap]
  exact realizeListChain_smallProjection_inclusion U A σ.val σ.property _ _ _

/-- The original small differential and the restricted homotopy satisfy the
actual degree-zero homotopy equation. -/
theorem smallBarycentricHomotopyMap_d_zero (U : ι → Set X) (A : System.{u, u} X) :
    smallBarycentricHomotopyMap U A 0 ≫ (smallChainComplex U A).d 1 0 =
      𝟙 _ - smallBarycentricSubdivisionMap U A 0 := by
  apply (cancel_mono (smallModuleInclusion U A ⦋0⦌)).mp
  have comm := ((smallChainComplexInclusion U A).comm 1 0).symm
  change (smallChainComplex U A).d 1 0 ≫ smallModuleInclusion U A ⦋0⦌ =
    smallModuleInclusion U A ⦋1⦌ ≫ (singularChainComplex A).d 1 0 at comm
  simp only [Category.assoc, comm, smallBarycentricHomotopyMap_inclusion_assoc,
    Preadditive.sub_comp, Category.id_comp, smallBarycentricSubdivisionMap_inclusion]
  rw [barycentricHomotopyMap_d_zero, Preadditive.comp_sub, Category.comp_id]

/-- The restricted coning homotopy satisfies the actual equation in positive degrees. -/
theorem smallBarycentricHomotopyMap_d (U : ι → Set X) (A : System.{u, u} X) (n : ℕ) :
    smallBarycentricHomotopyMap U A (n + 1) ≫ (smallChainComplex U A).d (n + 2) (n + 1) +
        (smallChainComplex U A).d (n + 1) n ≫ smallBarycentricHomotopyMap U A n =
      𝟙 _ - smallBarycentricSubdivisionMap U A (n + 1) := by
  apply (cancel_mono (smallModuleInclusion U A ⦋n + 1⦌)).mp
  have comm (i j : ℕ) := ((smallChainComplexInclusion U A).comm i j).symm
  change ∀ i j, (smallChainComplex U A).d i j ≫ smallModuleInclusion U A ⦋j⦌ =
    smallModuleInclusion U A ⦋i⦌ ≫ (singularChainComplex A).d i j at comm
  simp only [Preadditive.add_comp, Preadditive.sub_comp, Category.assoc,
    comm, smallBarycentricHomotopyMap_inclusion_assoc,
    smallBarycentricHomotopyMap_inclusion, Category.id_comp,
    smallBarycentricSubdivisionMap_inclusion]
  rw [← Category.assoc ((smallChainComplex U A).d (n + 1) n), comm,
    Category.assoc, ← Preadditive.comp_add, barycentricHomotopyMap_d,
    Preadditive.comp_sub, Category.comp_id]

/-- The constructed barycentric subdivision of cover-small chains is homotopic
 to their identity through the restriction of the actual geometric homotopy. -/
def smallBarycentricSubdivisionHomotopy (U : ι → Set X) (A : System.{u, u} X) :
    Homotopy (𝟙 (smallChainComplex U A)) (smallBarycentricSubdivision U A) :=
  ChainComplex.homotopyOfDegreeRaising (smallBarycentricSubdivision U A)
    (smallBarycentricHomotopyMap U A) (smallBarycentricHomotopyMap_d_zero U A)
    (smallBarycentricHomotopyMap_d U A)

end FundamentalGroupoid.LocalCoefficients
