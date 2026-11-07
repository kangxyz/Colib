/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.CubicalSubdivision.FaceBoundaryTopology
public import Colib.Topology.CubicalSubdivision.Walls

/-! # Literal finite cube-boundary lifting and its face-coordinate adapter

The lifting condition uses the original unlifted cube coordinates and permits
independent source/target universes. Genuine TopCat lifting in any common
universe implies it by the actual ULift coordinate maps.


Implementation provenance:
`Quillen/Topology/CubicalSubdivision/BoundaryLifting.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open CategoryTheory
open scoped Topology unitInterval
namespace Topology.CubicalSubdivision
universe u v

/-- Strict right lifting against every actual finite cube boundary, stated
in original coordinates without a universe restriction on the target. -/
def BoundaryLifting {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) : Prop :=
  ∀ (n : ℕ) (a : C(Boundary n,E)) (b : C(Cube n,B)),
    (∀ t : Boundary n,p (a t) = b t) →
      ∃ c : C(Cube n,E), (∀ t : Boundary n,c t = a t) ∧ p.comp c = b

/-- Actual lifted-boundary RLP supplies the original-coordinate condition;
only the cube and boundary parameters are universe-lifted. -/
theorem boundaryLifting_of_hasLiftingProperty
    {E B : Type u} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (hp : ∀ n, HasLiftingProperty (CubicalTests.boundaryInclusion.{u} n) (TopCat.ofHom p)) :
    BoundaryLifting p := by
  intro n a b hab
  let a' : TopCat.of (CubicalTests.boundary.{u} n) ⟶ TopCat.of E :=
    TopCat.ofHom ⟨fun t ↦ a ⟨t.val.down,t.2⟩,by fun_prop⟩
  let b' : CubicalTests.cube.{u} n ⟶ TopCat.of B :=
    TopCat.ofHom ⟨fun t ↦ b t.down,by fun_prop⟩
  let : HasLiftingProperty (CubicalTests.boundaryInclusion.{u} n) (TopCat.ofHom p) := hp n
  let sq : CommSq a' (CubicalTests.boundaryInclusion n) (TopCat.ofHom p) b' := ⟨by
    ext t : 1
    exact hab ⟨t.val.down,t.2⟩⟩
  let c : C(Cube n,E) := ⟨fun t ↦ sq.lift (ULift.up t),by fun_prop⟩
  refine ⟨c,?_,?_⟩
  · intro t
    exact ConcreteCategory.congr_hom sq.fac_left ⟨⟨t.val⟩,t.2⟩
  · apply ContinuousMap.ext
    intro t
    exact ConcreteCategory.congr_hom sq.fac_right (ULift.up t)

/-- Remove the lifts from the genuine finite-coordinate homeomorphism. -/
def faceParamHomeomorph {n m : ℕ} (F : FaceIndex n m) :
    (Active F → unitInterval) ≃ₜ Cube (faceDimension F) :=
  (Homeomorph.ulift.{0,0} (X := Active F → unitInterval)).symm |>.trans
    (faceCubeHomeomorph.{0} F) |>.trans
    (Homeomorph.ulift.{0,0} (X := Cube (faceDimension F)))

/-- The corresponding exact raw boundary homeomorphism. -/
def faceParamBoundaryHomeomorph {n m : ℕ} (F : FaceIndex n m) :
    {t : Active F → unitInterval // t ∈ _root_.Cube.boundary (Active F)} ≃ₜ
      Boundary (faceDimension F) :=
  (faceBoundaryUnliftedHomeomorph.{0} F).symm |>.trans
    (faceCubeBoundaryHomeomorph.{0} F) |>.trans
    (CubicalTests.boundaryULiftHomeomorph.{0} (faceDimension F))

@[simp] theorem faceParamBoundaryHomeomorph_val {n m : ℕ} (F : FaceIndex n m)
    (t : {t : Active F → unitInterval // t ∈ _root_.Cube.boundary (Active F)}) :
    (faceParamBoundaryHomeomorph F t).val = faceParamHomeomorph F t.val := rfl

@[simp] theorem faceParamBoundaryHomeomorph_symm_val {n m : ℕ} (F : FaceIndex n m)
    (t : Boundary (faceDimension F)) :
    ((faceParamBoundaryHomeomorph F).symm t).val = (faceParamHomeomorph F).symm t.val := rfl

/-- Strict finite boundary lifting applies to every actual face parameter
space, preserving its entire original boundary map. -/
theorem BoundaryLifting.face {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    {p : C(E, B)} (hp : BoundaryLifting p) {n m : ℕ} (F : FaceIndex n m)
    (a : C({t : Active F → unitInterval // t ∈ _root_.Cube.boundary (Active F)}, E))
    (b : C((Active F → unitInterval), B))
    (hab : ∀ t, p (a t) = b t) :
    ∃ c : C((Active F → unitInterval),E),
      (∀ t : {t : Active F → unitInterval // t ∈ _root_.Cube.boundary (Active F)},c t = a t) ∧
        p.comp c = b := by
  let e := faceParamHomeomorph F
  let d := faceParamBoundaryHomeomorph F
  let a' := a.comp d.symm.toHomotopyEquiv.toFun
  let b' := b.comp e.symm.toHomotopyEquiv.toFun
  have h : ∀ t : Boundary (faceDimension F),p (a' t) = b' t := fun t ↦ hab (d.symm t)
  obtain ⟨c,hc,he⟩ := hp (faceDimension F) a' b' h
  refine ⟨c.comp e.toHomotopyEquiv.toFun,?_,?_⟩
  · intro t
    have hh := hc (d t)
    change c (e t.val) = a (d.symm (d t)) at hh
    change c (e t.val) = a t
    simpa only [Homeomorph.symm_apply_apply] using hh
  · apply ContinuousMap.ext
    intro t
    have hh := ContinuousMap.congr_fun he (e t)
    change p (c (e t)) = b (e.symm (e t)) at hh
    change p (c (e t)) = b t
    simpa only [Homeomorph.symm_apply_apply] using hh

end Topology.CubicalSubdivision
