/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Additivity.RealizationHomotopy
public import Colib.KTheory.Waldhausen.Map
public import Colib.CategoryTheory.Waldhausen.SConstruction.Bisimplicial

/-! # The actual diagonal realization comparison square

Extracted from Quillen/Waldhausen/Additivity/RealizedAdditivity.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd. This naturality theorem uses only the
existing simplicial diagonal isomorphism, and does not depend on additivity.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u v
namespace CategoryTheory.Waldhausen.Additivity
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (V : Structure C) (W : Structure D)

/-- The exact diagonal identification respects the original realized S-map. -/
theorem realizedDiagonalMap_exact_naturality {J : C ⥤ D}
    (hJ : IsExact V.cof V.weq W.cof W.weq J) :
    (SSet.toTop.map (bisimplicialDiagonalIso W).hom).hom.comp
        (realizedDiagonalMap (bisimplicialSSetMap V.cof V.weq hJ)) =
      (deloopingMap hJ).hom.comp (SSet.toTop.map (bisimplicialDiagonalIso V).hom).hom := by
  have h := congrArg SSet.toTop.map (bisimplicialDiagonalIso_naturality V.cof V.weq hJ)
  rw [Functor.map_comp, Functor.map_comp] at h
  exact congrArg TopCat.Hom.hom h


end CategoryTheory.Waldhausen.Additivity
