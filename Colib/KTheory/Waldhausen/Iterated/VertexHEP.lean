/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.VertexHEP
public import Colib.KTheory.Waldhausen.Iterated.Prespectrum

/-!
# Well-based positive levels of the original iterated-S spectrum

Each positive original level is the realization of its actual simplicial stage, with the literal
chosen zero vertex. Its singleton inclusion has HEP by the genuine realized-vertex theorem.
-/
/-! Implementation provenance: `Quillen/Waldhausen/SConstruction/Iterated/VertexHEP.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original maps, full null track, degree bounds, signed boundary and independent
object/hom universes are retained using the native strict chosen-zero subcategory. -/
@[expose] public section
noncomputable section

open CategoryTheory
universe u v
namespace CategoryTheory.Waldhausen.IteratedS
open Topology SmallWaldhausenCategory

/-- The chosen point of each actual positive S-spectrum level has a genuine HEP inclusion. -/
theorem originalPrespectrum_positivePoint_homotopyExtensionProperty
    {C : Type u} [Category.{v} C] (W : Structure C) (n : ℕ) :
    TopCat.HomotopyExtensionProperty (TopCat.ofHom
      (ContinuousMap.const PUnit.{max u v + 1} ((originalPrespectrum W).point (n + 1)))) :=
  SSet.homotopyExtensionProperty_vertex (stageVertex n (asSmallCategory W))

end CategoryTheory.Waldhausen.IteratedS
