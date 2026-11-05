/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.FiniteSubcomplex
public import Colib.Topology.Realization.Prism

/-! # Genuine compactness of finite simplicial realizations

Every realization point lies in the image of an actual nondegenerate simplex.
For a finite simplicial set, this gives a finite compact cover, without a
Hausdorff or local-compactness hypothesis on the whole realization.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Simplicial Topology
universe u

namespace SSet

/-- The actual maps of nondegenerate simplices jointly cover the realization. -/
theorem realization_nonDegenerate_jointly_surjective (X : SSet.{u}) (x : |X|) :
    ∃ (s : X.N) (t : |(Δ[s.dim] : SSet.{u})|),
      SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex) t = x := by
  obtain ⟨n, f, t, rfl⟩ := realization_exists_simplex x
  obtain ⟨m, g, _, y, hy⟩ := X.exists_nonDegenerate (SSet.yonedaEquiv f)
  refine ⟨SSet.N.mk y.1 y.2, SSet.toTop.map (SSet.stdSimplex.map g) t, ?_⟩
  change (SSet.toTop.map (SSet.stdSimplex.map g) ≫
    SSet.toTop.map (SSet.yonedaEquiv.symm y.1)) t = _
  rw [← CategoryTheory.Functor.map_comp]
  have he : SSet.stdSimplex.map g ≫ SSet.yonedaEquiv.symm y.1 = f := by
    apply SSet.yonedaEquiv.injective
    simpa only [← SSet.yonedaEquiv_naturality, Equiv.apply_symm_apply] using hy.symm
  rw [he]

/-- A finite simplicial set has a genuinely compact topological realization. -/
instance realizationFinite_compactSpace (X : SSet.{u}) [X.Finite] : CompactSpace |X| := by
  let f : (Σ s : X.N, |(Δ[s.dim] : SSet.{u})|) → |X| :=
    fun z ↦ SSet.toTop.map (SSet.yonedaEquiv.symm z.1.simplex) z.2
  have hf : Continuous f := by
    apply continuous_sigma
    intro s
    exact (SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)).hom.continuous
  exact Function.Surjective.compactSpace hf (fun x ↦ by
    obtain ⟨s, t, ht⟩ := realization_nonDegenerate_jointly_surjective X x
    exact ⟨⟨s, t⟩, ht⟩)

end SSet
