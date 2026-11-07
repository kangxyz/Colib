/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.TheoremA.SkeletalHomology
public import Colib.Topology.LocalCoefficients.FilteredComparison

/-!
Adapted from `Quillen/CategoryTheory/TheoremA/ReplacementHomology.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps.

# Original twisted homology comparison of realized simplicial replacements

The actual all-dimensional skeletal comparison passes through the exhaustive
simplicial colimit using the original spatial chain and homology maps. Every
possibly nonconstant abelian-monodromy target system is allowed.
-/

@[expose] public section
noncomputable section
open SSet TopCat Convexity.StdSimplex
open CategoryTheory Limits FundamentalGroupoid.LocalCoefficients
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.TheoremA
variable {D : Type u} [SmallCategory D] {H K : D ⥤ SSet.{u}}

/-- Objectwise abelian homology comparison induces comparison of the original
realized simplicial-replacement map, for every abelian target local system. -/
theorem replacementRealization_abelian_quasiIso (η : H ⟶ K)
    (hη : ∀ (d : D) (A : System.{u, u} |K.obj d|), AbelianMonodromy A →
      QuasiIso (pushforwardChainMap (SSet.toTop.map (η.app d)).hom A))
    (A : System.{u, u} |replacementDiagonal K|) (hA : AbelianMonodromy A) :
    QuasiIso (pushforwardChainMap
      (SSet.toTop.map (diagonalMap (simplicialReplacementMap η))).hom A) := by
  let F := replacementSkeleton H ⋙ diagonalFunctor
  let G := replacementSkeleton K ⋙ diagonalFunctor
  let c := diagonalFunctor.mapCocone (replacementSkeletonCocone H)
  let d := diagonalFunctor.mapCocone (replacementSkeletonCocone K)
  let τ := Functor.whiskerRight (replacementSkeletonMap η) diagonalFunctor
  let f := diagonalMap (simplicialReplacementMap η)
  have w (n : ℕ) : c.ι.app n ≫ f = τ.app n ≫ d.ι.app n := by
    exact (congrArg diagonalFunctor.map (replacementSkeletonMap_ι η n)).symm.trans
      (by rw [Functor.map_comp]; rfl)
  have hc : IsColimit c := isColimitOfPreserves diagonalFunctor (replacementSkeletonIsColimit H)
  have hd : IsColimit d := isColimitOfPreserves diagonalFunctor (replacementSkeletonIsColimit K)
  apply sequentialComparison_pushforwardChainMap_quasiIso F G c d τ f w hc hd A
  intro n
  exact replacementSkeletonStageMap_abelian_quasiIso η hη n
    (pullback (SSet.toTop.map (d.ι.app n)).hom A)
    (pullback_abelianMonodromy (SSet.toTop.map (d.ι.app n)).hom hA)

end CategoryTheory.TheoremA
