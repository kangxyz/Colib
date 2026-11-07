/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.TheoremA.AttachmentNaturality
public import Colib.Topology.LocalCoefficients.EmbeddingSquareChains

/-!
Adapted from `Quillen/CategoryTheory/TheoremA/SkeletalHomology.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps.

# Actual twisted homology comparison on replacement skeleta

Objectwise abelian twisted homology comparisons induce quasi-isomorphisms on
every original realized skeletal stage. The proof uses the actual characteristic
pair maps, their original quotient squares, and the short exact chain sequences
of the genuine topological embeddings. The empty zeroth stage is included.
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

/-- The map on the cokernels of the original successor chain inclusions. -/
def replacementSkeletonCokernelMap (η : H ⟶ K) (n : ℕ)
    (A : System.{u, u} ((realizedReplacementSkeleton K).obj (n + 1))) :=
  embeddingSquareCokernelMap (replacementSkeletonStep H n) (replacementSkeletonStep K n)
    (replacementSkeletonStageMap η n) (replacementSkeletonStageMap η (n + 1))
    (replacementSkeletonStep_square η n) A

/-- The original cokernel map is the actual relative range-pair map in the embedding coordinates. -/
theorem replacementSkeletonCokernelMap_eq (η : H ⟶ K) (n : ℕ)
    (A : System.{u, u} ((realizedReplacementSkeleton K).obj (n + 1))) :
    replacementSkeletonCokernelMap η n A =
      (embeddingCokernelIsoRelative (replacementSkeletonStep H n)
        (replacementSkeletonStep_isClosedEmbedding H n).isEmbedding
        (pullback (replacementSkeletonStageMap η (n + 1)) A)).hom ≫
      replacementSkeletonRangeRelativeMap η n A ≫
      (embeddingCokernelIsoRelative (replacementSkeletonStep K n)
        (replacementSkeletonStep_isClosedEmbedding K n).isEmbedding A).inv := by
  apply (cancel_epi (cokernel.π (pushforwardChainMap (replacementSkeletonStep H n)
    (pullback (replacementSkeletonStageMap η (n + 1)) A)))).mp
  dsimp only [replacementSkeletonCokernelMap, replacementSkeletonRangeRelativeMap]
  rw [embeddingSquareCokernelMap_quotient,
    embeddingCokernelIsoRelative_quotient_assoc,
    ← Category.assoc, relativePushforwardChainMap_quotient, Category.assoc,
    ← embeddingCokernelIsoRelative_quotient (replacementSkeletonStep K n)
      (replacementSkeletonStep_isClosedEmbedding K n).isEmbedding A,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Objectwise abelian comparison induces a quasi-isomorphism on the original stage cokernels. -/
theorem replacementSkeletonCokernelMap_quasiIso (η : H ⟶ K)
    (hη : ∀ (d : D) (A : System.{u, u} |K.obj d|), AbelianMonodromy A →
      QuasiIso (pushforwardChainMap (SSet.toTop.map (η.app d)).hom A))
    (n : ℕ) (A : System.{u, u} ((realizedReplacementSkeleton K).obj (n + 1)))
    (hA : AbelianMonodromy A) : QuasiIso (replacementSkeletonCokernelMap η n A) := by
  rw [replacementSkeletonCokernelMap_eq]
  have := replacementSkeletonRangeRelativeMap_quasiIso η hη n A hA
  infer_instance

/-- Every original realized skeleton map preserves homology with every abelian target system. -/
theorem replacementSkeletonStageMap_abelian_quasiIso (η : H ⟶ K)
    (hη : ∀ (d : D) (A : System.{u, u} |K.obj d|), AbelianMonodromy A →
      QuasiIso (pushforwardChainMap (SSet.toTop.map (η.app d)).hom A))
    (n : ℕ) (A : System.{u, u} ((realizedReplacementSkeleton K).obj n))
    (hA : AbelianMonodromy A) :
    QuasiIso (pushforwardChainMap (replacementSkeletonStageMap η n) A) := by
  induction n with
  | zero =>
    let e := TopCat.homeoOfIso (asIso ((realizedReplacementSkeletonMap η).app 0))
    have := pushforwardChainMap_isIso_of_homeomorph e A
    change QuasiIso (pushforwardChainMap (toContinuousMap e) A)
    infer_instance
  | succ n ih =>
    apply pushforwardChainMap_quasiIso_of_embeddingSquare
      (replacementSkeletonStep H n) (replacementSkeletonStep K n)
      (replacementSkeletonStageMap η n) (replacementSkeletonStageMap η (n + 1))
      (replacementSkeletonStep_square η n) A
      (replacementSkeletonStep_isClosedEmbedding H n).isEmbedding
      (replacementSkeletonStep_isClosedEmbedding K n).isEmbedding
    · exact ih (pullback (replacementSkeletonStep K n) A)
        (pullback_abelianMonodromy (replacementSkeletonStep K n) hA)
    · exact replacementSkeletonCokernelMap_quasiIso η hη n A hA

end CategoryTheory.TheoremA
