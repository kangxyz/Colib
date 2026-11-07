/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.LocalTrivializations
public import Colib.CategoryTheory.NaturalTransformation.Transport

/-!
# Restriction

Restriction of an actual chart natural isomorphism to a common subchart.
The source functor is normalized to the actual ambient inclusion.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set CategoryTheory
universe u v w
namespace FundamentalGroupoid.OpenCover

/-- Restriction of an actual chart natural isomorphism to a common subchart.
The source functor is normalized to the actual ambient inclusion. -/
def restrictChartIso {X : Type u} [TopologicalSpace X] {C : Type v} [Category.{w} C]
    (F : FundamentalGroupoid X ⥤ C) (b : C) (S U : Set X) (h : S ⊆ U)
    (η : FundamentalGroupoid.map ((ContinuousMap.subtypeVal ((fun _ : Unit => U) ()))) ⋙ F ≅
      (Functor.const (FundamentalGroupoid U)).obj b) :
    FundamentalGroupoid.map ((ContinuousMap.subtypeVal ((fun _ : Unit => S) ()))) ⋙ F ≅
      (Functor.const (FundamentalGroupoid S)).obj b := by
  let k := (ContinuousMap.inclusion h)
  have hf : FundamentalGroupoid.map k ⋙
      (FundamentalGroupoid.map ((ContinuousMap.subtypeVal ((fun _ : Unit => U) ()))) ⋙ F) =
      FundamentalGroupoid.map ((ContinuousMap.subtypeVal ((fun _ : Unit => S) ()))) ⋙ F := by
    rw [← Functor.assoc, ← FundamentalGroupoid.map_comp]
    rfl
  exact cast (congrArg (fun K => K ≅ (Functor.const (FundamentalGroupoid S)).obj b) hf)
    (Functor.isoWhiskerLeft (FundamentalGroupoid.map k) η)

/-- Restriction preserves the literal original component at each subchart point. -/
theorem restrictChartIso_hom_app {X : Type u} [TopologicalSpace X]
    {C : Type v} [Category.{w} C]
    (F : FundamentalGroupoid X ⥤ C) (b : C) (S U : Set X) (h : S ⊆ U)
    (η : FundamentalGroupoid.map ((ContinuousMap.subtypeVal ((fun _ : Unit => U) ()))) ⋙ F ≅
      (Functor.const (FundamentalGroupoid U)).obj b) (x : S) :
    (restrictChartIso F b S U h η).hom.app (FundamentalGroupoid.mk x) =
      η.hom.app (FundamentalGroupoid.mk ((ContinuousMap.inclusion h) x)) := by
  let k := (ContinuousMap.inclusion h)
  have hf : FundamentalGroupoid.map k ⋙
      (FundamentalGroupoid.map ((ContinuousMap.subtypeVal ((fun _ : Unit => U) ()))) ⋙ F) =
      FundamentalGroupoid.map ((ContinuousMap.subtypeVal ((fun _ : Unit => S) ()))) ⋙ F := by
    rw [← Functor.assoc, ← FundamentalGroupoid.map_comp]
    rfl
  change (cast (congrArg (fun K => K ≅ (Functor.const (FundamentalGroupoid S)).obj b) hf)
    (Functor.isoWhiskerLeft (FundamentalGroupoid.map k) η)).hom.app _ = _
  rw [natIso_transport_hom_app hf]
  change eqToHom _ ≫ η.hom.app (FundamentalGroupoid.mk (k x)) = _
  rw [eqToHom_refl, Category.id_comp]

end FundamentalGroupoid.OpenCover
