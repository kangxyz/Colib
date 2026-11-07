/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.HomeomorphismChains
public import Colib.Topology.LocalCoefficients.MapComposition
public import Colib.Topology.LocalCoefficients.RelativeAcyclicity
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
Adapted from `Quillen/Topology/LocalCoefficients/EmbeddingRelativeChains.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps.
 # Actual embedding cokernels and relative chains of the image subspace -/
@[expose] public section
noncomputable section
open CategoryTheory Limits
universe u
namespace FundamentalGroupoid.LocalCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  (j : C(X, Y)) (hj : Topology.IsEmbedding j) (A : System.{u, u} Y)

/-- The original domain's chains identify with the actual image-subspace chains. -/
def embeddingRangeChainIso :
    singularChainComplex (pullback j A) ≅
      singularChainComplex (pullback (subspaceInclusion (Set.range j)) A) :=
  coefficientChainIso
    (pullbackCompositionIso (toContinuousMap hj.toHomeomorph)
      (subspaceInclusion (Set.range j)) A) ≪≫
    homeomorphismChainIso hj.toHomeomorph (pullback (subspaceInclusion (Set.range j)) A)

/-- The image identification retains the original spatial chain map. -/
@[reassoc]
theorem embeddingRangeChainIso_inclusion :
    (embeddingRangeChainIso j hj A).hom ≫
      pushforwardChainMap (subspaceInclusion (Set.range j)) A =
        pushforwardChainMap j A := by
  change (coefficientChainMap (pullbackCompositionIso (toContinuousMap hj.toHomeomorph)
    (subspaceInclusion (Set.range j)) A).hom ≫
      pushforwardChainMap (toContinuousMap hj.toHomeomorph)
        (pullback (subspaceInclusion (Set.range j)) A)) ≫ _ = _
  rw [Category.assoc, ← pushforwardChainMap_comp]
  rfl

/-- Cokernels of actual embedding chain maps are the relative complexes of their actual ranges. -/
def embeddingCokernelIsoRelative :
    cokernel (pushforwardChainMap j A) ≅ relativeSingularChainComplex (Set.range j) A :=
  cokernel.mapIso (pushforwardChainMap j A)
    (pushforwardChainMap (subspaceInclusion (Set.range j)) A)
    (embeddingRangeChainIso j hj A) (Iso.refl _)
    (by simpa only [Iso.refl_hom, Category.comp_id] using
      (embeddingRangeChainIso_inclusion j hj A).symm)

/-- The cokernel identification leaves the original quotient map unchanged. -/
@[reassoc]
theorem embeddingCokernelIsoRelative_quotient :
    cokernel.π (pushforwardChainMap j A) ≫ (embeddingCokernelIsoRelative j hj A).hom =
      cokernel.π (pushforwardChainMap (subspaceInclusion (Set.range j)) A) := by
  simp [embeddingCokernelIsoRelative, cokernel.mapIso_hom]

end FundamentalGroupoid.LocalCoefficients
