/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.FilteredRealization.HELP
public import Colib.Topology.HELP.HomotopyEquiv

/-! Actual filtered colimit legs satisfy compact HELP, including the exact
prescribed boundary homotopy, by factorization through a later actual HE. -/
/-! Implementation provenance: adapted from
`Quillen/Topology/FilteredRealization/CompactHELP.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps, homotopies,
hypotheses and universes are retained; imports use native lower owners. -/
@[expose] public section

noncomputable section
universe u
open TopCat Topology SSet Convexity.StdSimplex CategoryTheory Limits
open scoped Simplicial Topology unitInterval
set_option backward.isDefEq.respectTransparency false
namespace Topology.FilteredRealization
variable {J : Type u} [SmallCategory J] [IsFiltered J]
  (F : J ⥤ SSet.{u}) (c : Cocone F) (hc : IsColimit c)

include hc
/-- The compact HELP property of the actual stage-to-colimit map. This is
stronger than a statement about homotopy groups: it retains the whole given
boundary map and the complete boundary homotopy, exactly. -/
theorem stage_compactHELP
    (e : ∀ {j k : J} (_ : j ⟶ k), ContinuousMap.HomotopyEquiv |F.obj j| |F.obj k|)
    (he : ∀ {j k : J} (u : j ⟶ k), (e u).toFun = (SSet.toTop.map (F.map u)).hom)
    (j : J) : CompactHomotopyExtensionLiftingProperty (SSet.toTop.map (c.ι.app j)).hom := by
  intro A B _ _ i hi a b H
  obtain ⟨k,u,b',K,hb',hK⟩ := compact_square_homotopy_factors F c hc j i.hom a b H
  let E : ContinuousMap.HomotopyEquiv |F.obj j| |F.obj k| := {
    e u with
    toFun := (SSet.toTop.map (F.map u)).hom
    left_inv := by simpa only [he u] using (e u).left_inv
    right_inv := by simpa only [he u] using (e u).right_inv }
  obtain ⟨a',ha',L,hL⟩ := TopCat.homotopyEquiv_HELP hi E a b' K
  have hcomp : (SSet.toTop.map (c.ι.app k)).hom.comp
      ((SSet.toTop.map (F.map u)).hom.comp a') =
      (SSet.toTop.map (c.ι.app j)).hom.comp a' := by
    ext x
    change (SSet.toTop.map (F.map u) ≫ SSet.toTop.map (c.ι.app k)) (a' x) = _
    rw [← Functor.map_comp,c.w]
    rfl
  let L' := ((ContinuousMap.Homotopy.refl (SSet.toTop.map (c.ι.app k)).hom).comp L).cast hcomp hb'
  refine ⟨a',ha',L',?_⟩
  intro t x
  change SSet.toTop.map (c.ι.app k) (L (t,i x)) = H (t,x)
  rw [hL]
  exact hK t x

end Topology.FilteredRealization
