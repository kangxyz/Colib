/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.EmbeddingRelativeChains
public import Colib.Topology.LocalCoefficients.MapSquares
public import Colib.Algebra.Homology.HomologicalComplex.QuasiIsoMiddle

/-!
Adapted from `Quillen/Topology/LocalCoefficients/EmbeddingSquareChains.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps.

# Actual cokernel chain maps of commuting embedding squares

The left vertical map carries the prescribed coefficient pullback isomorphism.
The middle and quotient maps retain the original spatial map. Short exactness
then gives the middle quasi-isomorphism from the two outer comparisons.
-/

@[expose] public section

noncomputable section
open CategoryTheory Limits
universe u

namespace FundamentalGroupoid.LocalCoefficients

variable {X₀ X₁ Y₀ Y₁ : Type u}
    [TopologicalSpace X₀] [TopologicalSpace X₁]
    [TopologicalSpace Y₀] [TopologicalSpace Y₁]
    (j : C(X₀, X₁)) (k : C(Y₀, Y₁)) (a : C(X₀, Y₀)) (b : C(X₁, Y₁))
    (w : b.comp j = k.comp a) (A : System.{u, u} Y₁)

/-- The corrected original left map in the actual spatial chain square. -/
def embeddingSquareLeftChainMap :
    singularChainComplex (pullback j (pullback b A)) ⟶
      singularChainComplex (pullback k A) :=
  coefficientChainMap (pullbackSquareIso j k a b w A).hom ≫
    pushforwardChainMap a (pullback k A)

/-- The actual map between the cokernels of the two original inclusion maps. -/
def embeddingSquareCokernelMap :
    cokernel (pushforwardChainMap j (pullback b A)) ⟶
      cokernel (pushforwardChainMap k A) :=
  cokernel.map _ _ (embeddingSquareLeftChainMap j k a b w A)
    (pushforwardChainMap b A) (by
      simpa only [embeddingSquareLeftChainMap, Category.assoc] using
        (pushforwardChainMap_square j k a b w A).symm)

/-- The induced quotient map retains precisely the original ambient chain map. -/
@[reassoc]
theorem embeddingSquareCokernelMap_quotient :
    cokernel.π (pushforwardChainMap j (pullback b A)) ≫
        embeddingSquareCokernelMap j k a b w A =
      pushforwardChainMap b A ≫ cokernel.π (pushforwardChainMap k A) :=
  cokernel.π_desc _ _ _

/-- An actual topological embedding induces a monomorphism on twisted chains. -/
theorem pushforwardChainMap_mono_of_embedding (hj : Topology.IsEmbedding j)
    (B : System.{u, u} X₁) : Mono (pushforwardChainMap j B) := by
  rw [← embeddingRangeChainIso_inclusion j hj B]
  infer_instance

/-- The canonical coefficient isomorphism does not change whether the original
left spatial chain map is a quasi-isomorphism. -/
theorem embeddingSquareLeftChainMap_quasiIso
    (ha : QuasiIso (pushforwardChainMap a (pullback k A))) :
    QuasiIso (embeddingSquareLeftChainMap j k a b w A) := by
  change QuasiIso ((coefficientChainIso (pullbackSquareIso j k a b w A)).hom ≫ _)
  infer_instance

/-- Actual embedding pairs and the two outer comparisons imply a quasi-isomorphism
of the original ambient spatial map. This includes the nonnegative endpoint. -/
theorem pushforwardChainMap_quasiIso_of_embeddingSquare
    (hj : Topology.IsEmbedding j) (hk : Topology.IsEmbedding k)
    (ha : QuasiIso (pushforwardChainMap a (pullback k A)))
    (hc : QuasiIso (embeddingSquareCokernelMap j k a b w A)) :
    QuasiIso (pushforwardChainMap b A) := by
  let := pushforwardChainMap_mono_of_embedding j hj (pullback b A)
  let := pushforwardChainMap_mono_of_embedding k hk A
  let S := ShortComplex.mk (pushforwardChainMap j (pullback b A))
    (cokernel.π _) (cokernel.condition _)
  let T := ShortComplex.mk (pushforwardChainMap k A)
    (cokernel.π _) (cokernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  have hT : T.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  let φ : S ⟶ T :=
    { τ₁ := embeddingSquareLeftChainMap j k a b w A
      τ₂ := pushforwardChainMap b A
      τ₃ := embeddingSquareCokernelMap j k a b w A
      comm₁₂ := by
        simpa only [embeddingSquareLeftChainMap, Category.assoc] using
          pushforwardChainMap_square j k a b w A
      comm₂₃ := (embeddingSquareCokernelMap_quotient j k a b w A).symm }
  exact HomologicalComplex.quasiIso_middle_of_shortExact φ hS hT
    (embeddingSquareLeftChainMap_quasiIso j k a b w A ha) hc

end FundamentalGroupoid.LocalCoefficients
