/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.Regular.SmallModel
public import Colib.AlgebraicGeometry.KTheory.Comparison

/-!
# The canonical K-to-G equivalence on regular schemes with the resolution property

Quillen's proved resolution theorem applies to actual finite vector-bundle
resolutions. Native Stacks perfectness and bounded replacement supply those
resolutions on a quasi-compact regular scheme with the resolution
property. The forward homomorphism remains the original `Scheme.KToG` in every
nonnegative degree, including zero. No dimension bound or global projectivity
hypothesis is introduced.

Implementation provenance: the canonical factorization in
`Quillen/AlgebraicGeometry/Scheme/Regular/GeneralComparison.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`; its algebraic resolution premise is
here discharged using the native Stacks results, Tags 0FDC and 0F8E.
-/
@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.ExactCategory

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

/-- Actual finite coherent resolutions imply bijectivity of the original canonical map. -/
theorem schemeKToG_bijective_of_finite_resolutions (X : Scheme.{u})
    [IsLocallyNoetherian X]
    (h : (coherentExactStructure X).ResolutionHypothesis (coherentVectorBundle X)) (n : ℕ) :
    Function.Bijective (KToG X n) := by
  have h₁ := (vectorBundleSmallLiftExact X).KMap_bijective_of_mapQ_isEquivalence n
  have h₂ := Resolution.inclusionKMap_bijective
    (coherentExactStructure X).smallModel (coherentSmallVectorBundle X)
    (coherentSmallResolutionHypothesis X h) n
  change Function.Bijective ((vectorBundleToCoherentExact X).smallModel.KMap n)
  rw [← vectorBundleSmall_factor X, ExactFunctor.KMap_comp]
  exact h₂.comp h₁

attribute [colib_ref "Quillen1973" "Section 4, Corollary 1 and proof, pp. 109-110"
  "ingredient" "The resolution theorem for actual objectwise finite admissible resolutions"]
  schemeKToG_bijective_of_finite_resolutions

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [CompactSpace X]
  [AlgebraicGeometry.HasResolutionProperty X] (hX : AlgebraicGeometry.IsRegular X)

/-- The canonical comparison is bijective on every nonnegative K-group.
Local noetherianity is derived from regularity. -/
theorem KToG_regular_bijective (n : ℕ) :
    letI := AlgebraicGeometry.isLocallyNoetherian_of_isRegular hX
    Function.Bijective (KToG X n) := by
  letI := AlgebraicGeometry.isLocallyNoetherian_of_isRegular hX
  exact Modules.schemeKToG_bijective_of_finite_resolutions X
    (Modules.coherentResolutionHypothesis_of_regular X hX) n

/-- The genuine regular-scheme equivalence, with the original canonical forward map. -/
def KToGRegularEquiv (n : ℕ) :
    letI := AlgebraicGeometry.isLocallyNoetherian_of_isRegular hX
    K X n ≃* G X n := by
  letI := AlgebraicGeometry.isLocallyNoetherian_of_isRegular hX
  exact MulEquiv.ofBijective (KToG X n) (KToG_regular_bijective X hX n)

/-- The equivalence does not replace or renormalize the canonical comparison. -/
@[simp]
theorem KToGRegularEquiv_coe (n : ℕ) :
    letI := AlgebraicGeometry.isLocallyNoetherian_of_isRegular hX
    (↑(KToGRegularEquiv X hX n) : K X n →* G X n) = KToG X n := rfl

attribute [colib_tag "COL-0286",
  colib_ref "Quillen1973"
    "Section 7, subsection 1, equation (1.1) and following paragraph, p. 124"
    "adaptation" "The original canonical K-to-G map under quasi-compact regularity and the \
    resolution property; no separatedness or uniform dimension bound is assumed"]
  KToG_regular_bijective KToGRegularEquiv KToGRegularEquiv_coe

end AlgebraicGeometry.Scheme
