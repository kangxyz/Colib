/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.DescAcross
public import Colib.Topology.Realization.Cylinder

/-!
# Continuity on the original realization cylinder

A function on the interval times a realization is continuous exactly when its
restrictions to the original simplex cylinders are continuous. This uses the
proved preservation of topological colimits by product with the locally
compact interval. No general product-of-quotient-maps assertion is used.
-/

/-! Implementation source: `Quillen/Topology/Realization/CylinderContinuity.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using the native simplex colimit. -/
@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped Simplicial Topology unitInterval

universe u v

namespace SSet

/-- Continuity on the actual realization cylinder is detected on its original simplex cylinders. -/
theorem continuous_realizationCylinder_iff {X : SSet.{u}} {Z : Type v} [TopologicalSpace Z]
    (f : I × |X| → Z) :
    Continuous f ↔ ∀ (n : SimplexCategory) (s : X.obj (op n)),
      Continuous (fun z : I × Convexity.StdSimplex ℝ (Fin (n.len + 1)) ↦
        f (z.1, realizationSimplex s z.2)) := by
  constructor
  · intro hf n s
    exact hf.comp (continuous_fst.prodMk ((realizationSimplex s).continuous.comp continuous_snd))
  · intro hf
    have hc : Continuous (fun z : |X| × TopCat.I.{u} ↦ f (z.2.down, z.1)) := by
      apply (TopCat.continuous_iff_of_isColimit
        ((tensorRight TopCat.I).mapCocone (realizationSimplexCocone X))
        (isColimitOfPreserves (tensorRight TopCat.I) (realizationSimplexCoconeIsColimit X)) _).mpr
      intro j
      change Continuous (fun z : SimplexCategory.toTop.obj j.left × TopCat.I.{u} ↦
        f (z.2.down, (realizationSimplexCocone X).ι.app j z.1))
      have hp : Continuous (fun z : SimplexCategory.toTop.obj j.left × TopCat.I.{u} ↦
          (z.2.down, z.1.down)) := by fun_prop
      convert (hf j.left (SSet.yonedaEquiv j.hom)).comp hp using 1
      funext z
      rcases z with ⟨⟨t⟩, ⟨r⟩⟩
      change f (r, (realizationSimplexCocone X).ι.app j (ULift.up t)) =
        f (r, realizationSimplex (SSet.yonedaEquiv j.hom) t)
      rw [realizationSimplexCocone_ι_apply]
    exact hc.comp (continuous_snd.prodMk (continuous_uliftUp.comp continuous_fst))

end SSet
