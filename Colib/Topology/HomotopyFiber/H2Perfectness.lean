/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.InjectiveH2Perfectness
public import Colib.Topology.HomotopyFiber.WeakBasePositive
public import Colib.Topology.MappingCylinder.Embedding
public import Colib.Topology.LocalCoefficients.HomotopyEquivalence
public import Colib.Topology.LocalCoefficients.ConstantChainMaps
public import Colib.Topology.LocalCoefficients.IntegralChains
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Integral H-two surjectivity makes the actual homotopy-fiber group perfect

The genuine mapping cylinder replaces an arbitrary map by its embedded source
inclusion. Its actual projection is a homotopy equivalence, and preserves the
original composite and stated basepoints. Constant-coefficient functoriality
transfers H-two surjectivity to that inclusion. The endpoint-aware original
fiber comparison then transfers the proved injective-map criterion back to
the original homotopy fiber.
-/

/-! Implementation source: `Quillen/Topology/HomotopyFiber/H2Perfectness.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Genuine mapping-cylinder geometry
removes injectivity without changing the original homotopy fiber or basepoint. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory HomologicalComplex
universe u
namespace Topology.HomotopyFiber
open FundamentalGroupoid.LocalCoefficients TopCat

variable {X Y M : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace M]

/-- Actual H-two surjectivity cancels a genuine target homotopy equivalence. -/
theorem h2_surjective_of_composite_homotopyEquiv
    (j : C(X, M)) (e : ContinuousMap.HomotopyEquiv M Y) (f : C(X, Y))
    (h : e.toFun.comp j = f)
    (hH : Function.Surjective (pushforwardHomologyMap f
      (constant Y integralCoefficients.{u}) 2)) :
    Function.Surjective (pushforwardHomologyMap j
      (constant M integralCoefficients.{u}) 2) := by
  let rH := pushforwardHomologyMap e.toFun (constant Y integralCoefficients.{u}) 2
  have : IsIso rH := isIso_pushforwardHomologyMap_of_homotopyEquiv e _ _
  have hi := (ConcreteCategory.bijective_of_isIso rH).injective
  have hc : pushforwardHomologyMap f (constant Y integralCoefficients.{u}) 2 =
      pushforwardHomologyMap j (constant M integralCoefficients.{u}) 2 ≫ rH := by
    rw [← h, constant_pushforwardHomologyMap_comp]
  intro a
  obtain ⟨b, hb⟩ := hH (rH a)
  refine ⟨b, hi ?_⟩
  exact (ConcreteCategory.congr_hom hc b).symm.trans hb

/-- The original homotopy fiber has perfect Pi one when the source Pi one is perfect,
the source is path connected, the target is simply connected, and actual integral H two is onto. -/
theorem piOne_isPerfect_of_h2_surjective
    [PathConnectedSpace X] [SimplyConnectedSpace Y]
    (f : C(X, Y)) (x : X) [Group.IsPerfect (HomotopyGroup.Pi 1 X x)]
    (hH : Function.Surjective (pushforwardHomologyMap f
      (constant Y integralCoefficients.{u}) 2)) :
    Group.IsPerfect (HomotopyGroup.Pi 1 (HomotopyFiber f (f x))
      (basepoint f (f x) x rfl)) := by
  let A := TopCat.of X
  let B := TopCat.of Y
  let ft : A ⟶ B := TopCat.ofHom f
  let i := (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I)
  let M := pushout i ft
  let l : A ⊗ TopCat.I ⟶ M := pushout.inl i ft
  let c : B ⟶ M := pushout.inr i ft
  let sq : IsPushout i ft l c := IsPushout.of_hasPushout i ft
  let j := (TopCat.ι₀ ≫ l).hom
  let e := MappingCylinder.mappingCylinderProjectionHomotopyEquiv sq
  have hj : Function.Injective j := (MappingCylinder.mappingCylinderStart_isEmbedding sq).injective
  have he : e.toFun.comp j = f :=
    congrArg TopCat.Hom.hom (MappingCylinder.mappingCylinderProjection_start sq)
  let : SimplyConnectedSpace M := e.simplyConnectedSpace
  have hjH := h2_surjective_of_composite_homotopyEquiv j e f he hH
  let : Group.IsPerfect (HomotopyGroup.Pi 1 (HomotopyFiber j (j x))
      (basepoint j (j x) x rfl)) :=
    piOne_isPerfect_of_injective_of_h2_surjective j hj x hjH
  have hs : e.toFun.comp j = f.comp (ContinuousMap.id X) := by simpa using he
  have hb : e.toFun (j x) = f x := ContinuousMap.congr_fun he x
  have hb1 := (piMap_bijective_of_homotopyEquiv e hb 0).injective
  have hb2 := piMap_bijective_of_homotopyEquiv e hb 1
  have hm := mapAt_piOne_bijective j f e.toFun hs x (j x) rfl (f x) hb rfl hb1 hb2
  exact Group.IsPerfect.ofSurjective hm.surjective

/-- An actual integral chain quasi-isomorphism supplies the same criterion at any displayed
basepoint equality, with the original fiber and original constant-path basepoint. -/
theorem piOne_isPerfect_of_integral_quasiIso
    [PathConnectedSpace X] [SimplyConnectedSpace Y]
    (f : C(X, Y)) (y : Y) (x : X) (h : f x = y)
    [Group.IsPerfect (HomotopyGroup.Pi 1 X x)]
    (hq : QuasiIso (pushforwardChainMap f (constant Y integralCoefficients.{u}))) :
    Group.IsPerfect (HomotopyGroup.Pi 1 (HomotopyFiber f y) (basepoint f y x h)) := by
  subst y
  have : IsIso (pushforwardHomologyMap f (constant Y integralCoefficients.{u}) 2) :=
    (quasiIsoAt_iff_isIso_homologyMap _ 2).mp (hq.quasiIsoAt 2)
  exact piOne_isPerfect_of_h2_surjective f x (ConcreteCategory.bijective_of_isIso _).surjective

/-- The same conclusion for mathlib's original integral singular-chain map, transported
through the proved natural constant-coefficient chain isomorphisms. -/
theorem piOne_isPerfect_of_singular_quasiIso
    [PathConnectedSpace X] [SimplyConnectedSpace Y]
    (f : C(X, Y)) (y : Y) (x : X) (h : f x = y)
    [Group.IsPerfect (HomotopyGroup.Pi 1 X x)]
    (hq : QuasiIso (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj
      integralCoefficients.{u}).map (TopCat.ofHom f))) :
    Group.IsPerfect (HomotopyGroup.Pi 1 (HomotopyFiber f y) (basepoint f y x h)) := by
  let e : Arrow.mk (pushforwardChainMap f (constant Y integralCoefficients.{u})) ≅
      Arrow.mk (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj
        integralCoefficients.{u}).map (TopCat.ofHom f)) :=
    Arrow.isoMk (constantChainComplexIso (X := X) integralCoefficients.{u})
      (constantChainComplexIso (X := Y) integralCoefficients.{u})
      (constantChainComplexIso_naturality f integralCoefficients.{u}).symm
  exact piOne_isPerfect_of_integral_quasiIso f y x h
    ((quasiIso_iff_of_arrow_mk_iso _ _ e).mpr hq)

end Topology.HomotopyFiber
