/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.FilteredHomologyElements
public import Colib.Topology.LocalCoefficients.GrothendieckTelescope
public import Colib.Topology.LocalCoefficients.FiniteTelescope
public import Colib.Topology.LocalCoefficients.HomotopyInvariance

/-!
Adapted from `Quillen/Topology/LocalCoefficients/TelescopeHomologyElements.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original categorical maps.


# Actual stage representatives in the infinite categorical telescope

A finite-prefix representative is moved to its terminal stage using the
proved homotopy equivalence. Coefficient conversion is retained, so the final
representing map is precisely the original fiber inclusion into the infinite
Grothendieck model.
-/

@[expose] public section

open FundamentalGroupoid.LocalCoefficients


noncomputable section
open CategoryTheory Limits
universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace FundamentalGroupoid.LocalCoefficients

/-- If the first map is an actual local-homology isomorphism, every image under
the second map is represented under their literal composite. -/
theorem exists_pushforward_comp_of_isIso {X Y Z : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) (A : System.{u, u} Z) (k : ℕ)
    [IsIso (pushforwardHomologyMap f (pullback g A) k)]
    (x : homology (pullback g A) k) :
    ∃ y : homology (pullback (g.comp f) A) k,
      pushforwardHomologyMap (g.comp f) A k y = pushforwardHomologyMap g A k x := by
  let e := coefficientHomologyIso (pullbackCompositionIso f g A) k
  let m := pushforwardHomologyMap f (pullback g A) k
  refine ⟨e.inv (inv m x), ?_⟩
  rw [pushforwardHomologyMap_comp]
  change (pushforwardHomologyMap g A k) (m (e.hom (e.inv (inv m x)))) = _
  simp

end FundamentalGroupoid.LocalCoefficients

namespace CategoryTheory.Grothendieck.Telescope

open FundamentalGroupoid.LocalCoefficients

/-- Every class is represented at an original stage, not merely a finite prefix. -/
theorem localHomology_exists_stage (F : ℕ ⥤ Cat.{u, u})
    (A : System.{u, u} (ClassifyingSpace (Model F))) (k : ℕ) (x : homology A k) :
    ∃ (n : ℕ) (y : homology (pullback
      (classifyingSpaceMap (Grothendieck.ι F n)).hom A) k),
      pushforwardHomologyMap (classifyingSpaceMap (Grothendieck.ι F n)).hom A k y = x := by
  obtain ⟨j, z, hz⟩ := filteredHomology_exists_stage (prefixDiagram F ⋙ nerveFunctor)
    (nerveFunctor.mapCocone (prefixCocone F)) (nerveCoconeIsColimit F) A k x
  let n := AsSmall.down.obj j
  let f := (classifyingSpaceMap
    (CategoryTheory.Grothendieck.FiniteTelescope.inclusion F n (Fin.last n))).hom
  let g := (classifyingSpaceMap (prefixInclusion F n)).hom
  let := finiteTelescopeLastInclusion_isIso F n (pullback g A) k
  have hf : g.comp f = (classifyingSpaceMap (Grothendieck.ι F n)).hom := by
    exact congrArg TopCat.Hom.hom (fiber_prefix_classifying F n (Fin.last n))
  have hy := exists_pushforward_comp_of_isIso f g A k z
  rw [hf] at hy
  obtain ⟨y, hy⟩ := hy
  exact ⟨n, y, hy.trans hz⟩

end CategoryTheory.Grothendieck.Telescope
