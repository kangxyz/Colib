/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Path.PointHEP
public import Colib.KTheory.Waldhausen.Iterated.VertexHEP
public import Colib.KTheory.Waldhausen.Iterated.Separation

/-!
# Well-basedness of every original iterated-S level

Positive levels use the actual realized-vertex HEP theorem. The degree-zero
space is the original compact-open loop space of the first simplicial stage;
its chosen point has HEP by the proved loop-point theorem and the actual T1
separation of that realization. Thus the original model, including degree zero,
has a well-based chosen point at every level.
-/
/-! Implementation provenance: `Quillen/Waldhausen/SConstruction/Iterated/PointHEP.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original maps, full null track, degree bounds, signed boundary and independent
object/hom universes are retained using the native strict chosen-zero subcategory. -/
@[expose] public section

noncomputable section
open CategoryTheory
universe u v
namespace CategoryTheory.Waldhausen.IteratedS
open Topology SmallWaldhausenCategory

/-- Every chosen point of the actual iterated-S prespectrum has HEP, including its loop level. -/
theorem prespectrum_point_homotopyExtensionProperty
    (W : WideSubcategory preservesZero.{u}) (n : ℕ) :
    TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} ((prespectrum W).point n))) := by
  cases n with
  | zero =>
    exact Path.homotopyExtensionProperty_refl (x := stagePoint 0 W) isClosed_singleton
      (SSet.homotopyExtensionProperty_vertex (stageVertex 0 W))
  | succ r =>
    exact SSet.homotopyExtensionProperty_vertex (stageVertex r W)

/-- The original small-model S-prespectrum has HEP at its unchanged point in every degree. -/
theorem originalPrespectrum_point_homotopyExtensionProperty
    {C : Type u} [Category.{v} C] (W : Structure C) (n : ℕ) :
    TopCat.HomotopyExtensionProperty (TopCat.ofHom
      (ContinuousMap.const PUnit.{max u v + 1} ((originalPrespectrum W).point n))) :=
  prespectrum_point_homotopyExtensionProperty (asSmallCategory W) n

end CategoryTheory.Waldhausen.IteratedS
