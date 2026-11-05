/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.Topology.Realization.Basic
import Colib.Topology.Realization.Constant
import Colib.Topology.Realization.Simplex
import Colib.Topology.Realization.Cylinder
import Colib.Topology.Realization.SimplicialColimits

/-!
# Realization and cylinder prerequisite regression tests

These tests retain actual realized vertices, oriented interval endpoints and
independent diagram object/hom universes. The two colimit-preservation families
are tested separately; no realization-cylinder comparison isomorphism is claimed.
-/

open CategoryTheory Limits MonoidalCategory
open scoped Simplicial Topology unitInterval

universe u v w

noncomputable section

example {X : SSet.{u}} (x : X _⦋0⦌) :
    SSet.realizationPoint x = SSet.toTop.map (SSet.yonedaEquiv.symm x) default := rfl

example (t : unitInterval) : SSet.realizationInterval.{u} t =
    SSet.stdSimplex.toTopObjIsoI.inv (ULift.up t) := rfl

example : Continuous (SSet.realizationInterval.{u}) :=
  SSet.continuous_realizationInterval

example : SSet.realizationInterval.{u} 0 =
    SSet.toTop.map (SSet.stdSimplex.δ 1) default := SSet.realizationInterval_zero

example : SSet.realizationInterval.{u} 1 =
    SSet.toTop.map (SSet.stdSimplex.δ 0) default := SSet.realizationInterval_one

example {X Y : SSet.{u}} (y : Y _⦋0⦌) (x : |X|) :
    SSet.toTop.map (SSet.const y : X ⟶ Y) x = SSet.realizationPoint y :=
  SSet.realization_const_apply y x

example {X : SSet.{u}} (x : |X|) :
    ∃ (n : SimplexCategory) (f : SSet.stdSimplex.obj n ⟶ X)
      (t : |SSet.stdSimplex.obj n|), SSet.toTop.map f t = x :=
  SSet.realization_exists_simplex x

example (K : TopCat.{u}) [LocallyCompactSpace K] :
    tensorRight K ⊣ TopCat.topologicalMappingSpace K :=
  TopCat.topologicalProductMappingSpaceAdjunction K

example : PreservesColimitsOfSize.{v, w} (tensorRight TopCat.I.{u}) := inferInstance

example (X : SSet.{u}) (J : Type w) [Category.{v} J]
    [HasColimitsOfShape J (Type u)] : PreservesColimitsOfShape J (tensorLeft X) :=
  inferInstance

example (J : Type w) [Category.{v} J] [HasColimitsOfShape J (Type u)] :
    PreservesColimitsOfShape J (tensorRight (Δ[1] : SSet.{u})) := inferInstance

example (X : SSet.{u}) : PreservesColimits (tensorLeft X) := inferInstance

example : PreservesColimits (tensorRight (Δ[1] : SSet.{u})) := inferInstance

example (t : unitInterval) :
    SSet.stdSimplex.toTopObjIsoI.hom (SSet.realizationInterval.{u} t) = ULift.up t := by
  change (SSet.stdSimplex.toTopObjIsoI.inv ≫ SSet.stdSimplex.toTopObjIsoI.hom) _ = _
  rw [Iso.inv_hom_id]
  rfl

example (K Y : TopCat.{u}) : (TopCat.topologicalMappingSpace K).obj Y = TopCat.of C(K, Y) :=
  rfl

example (K Y Z : TopCat.{u}) (f : Y ⟶ Z) :
    (TopCat.topologicalMappingSpace K).map f =
      TopCat.ofHom ⟨ContinuousMap.comp f.hom, ContinuousMap.continuous_postcomp _⟩ := rfl
