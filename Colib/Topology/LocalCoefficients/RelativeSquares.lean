/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.MapSquares
public import Colib.Topology.LocalCoefficients.RelativeComposition

/-!
Adapted from `Quillen/Topology/LocalCoefficients/RelativeSquares.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps.

# Exact commuting squares on actual relative twisted chains

All objects are the actual subspace cokernel complexes. The square retains the
canonical original pullback isomorphism and is proved by the original quotient
equations and the actual absolute chain square.
-/

@[expose] public section
noncomputable section
open CategoryTheory Limits
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace FundamentalGroupoid.LocalCoefficients
variable {X Y Z T : Type u}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace T]

/-- The actual relative spatial maps retain the exact commuting coefficient-corrected square. -/
theorem relativePushforwardChainMap_square (f : C(X, Y)) (g : C(Z, T))
    (a : C(X, Z)) (b : C(Y, T)) (w : b.comp f = g.comp a)
    (U : Set X) (V : Set Y) (W : Set Z) (S : Set T)
    (hf : Set.MapsTo f U V) (hg : Set.MapsTo g W S)
    (ha : Set.MapsTo a U W) (hb : Set.MapsTo b V S) (A : System.{u, u} T) :
    relativeCoefficientChainMap U (pullbackSquareIso f g a b w A).hom ≫
        relativePushforwardChainMap a U W ha (pullback g A) ≫
          relativePushforwardChainMap g W S hg A =
      relativePushforwardChainMap f U V hf (pullback b A) ≫
        relativePushforwardChainMap b V S hb A := by
  apply (cancel_epi (cokernel.π
    (pushforwardChainMap (subspaceInclusion U) (pullback f (pullback b A))))).mp
  dsimp only [relativeSingularChainComplex]
  rw [relativeCoefficientChainMap_quotient_assoc]
  conv_lhs =>
    arg 2
    rw [← Category.assoc, relativePushforwardChainMap_quotient, Category.assoc,
      relativePushforwardChainMap_quotient]
  conv_rhs =>
    rw [← Category.assoc, relativePushforwardChainMap_quotient, Category.assoc,
      relativePushforwardChainMap_quotient]
  simpa only [Category.assoc] using congrArg
    (fun k ↦ k ≫ cokernel.π (pushforwardChainMap (subspaceInclusion S) A))
    (pushforwardChainMap_square f g a b w A)

end FundamentalGroupoid.LocalCoefficients
