/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.ComponentExtension
public import Colib.Topology.LocalCoefficients.SupportedChains
public import Colib.Topology.LocalCoefficients.MapSquares
public import Colib.Topology.LocalCoefficients.Homology
public import Mathlib.Algebra.Homology.QuasiIso

/-!
Adapted from `Quillen/Topology/LocalCoefficients/ComponentComparison.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using native Colib objects.

# Restriction of actual twisted homology equivalences to a specified component

Coefficients are extended by zero, and the two original component inclusions
are chain isomorphisms for these supported systems. The exact spatial square
then identifies the original restricted map. The preimage condition is stated
explicitly; no injectivity on components is inferred without proof.
-/

@[expose] public section

noncomputable section
open Topology CategoryTheory Limits
universe u

namespace FundamentalGroupoid.LocalCoefficients

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Changing the target system by its actual coefficient isomorphism preserves
quasi-isomorphism of the original spatial chain map. -/
theorem pushforwardChainMap_quasiIso_of_coefficientIso (f : C(X, Y))
    {A B : System.{u, u} Y} (e : A ≅ B)
    (hf : QuasiIso (pushforwardChainMap f A)) :
    QuasiIso (pushforwardChainMap f B) := by
  have hc : QuasiIso (coefficientChainMap (pullbackMap f e.hom)) := by
    change QuasiIso
      (coefficientChainIso (Functor.isoWhiskerLeft (FundamentalGroupoid.map f) e)).hom
    infer_instance
  have hcomp : QuasiIso (coefficientChainMap (pullbackMap f e.hom) ≫
      pushforwardChainMap f B) := by
    rw [pushforwardChainMap_coefficient_naturality]
    change QuasiIso (pushforwardChainMap f A ≫ (coefficientChainIso e).hom)
    infer_instance
  exact quasiIso_of_comp_left (coefficientChainMap (pullbackMap f e.hom))
    (pushforwardChainMap f B)

/-- An exact component preimage gives the literal restriction of the original map. -/
def componentMap (f : C(X, Y)) (x : X) (y : Y)
    (hpre : ∀ z, f z ∈ pathComponent y ↔ z ∈ pathComponent x) :
    C(pathComponent x, pathComponent y) :=
  ⟨fun z ↦ ⟨f z.val, (hpre z.val).mpr z.property⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- The original component square commutes strictly on underlying continuous maps. -/
theorem componentMap_square (f : C(X, Y)) (x : X) (y : Y)
    (hpre : ∀ z, f z ∈ pathComponent y ↔ z ∈ pathComponent x) :
    f.comp (subspaceInclusion (pathComponent x)) =
      (subspaceInclusion (pathComponent y)).comp (componentMap f x y hpre) := rfl

/-- Every local system on the specified target component is handled by an actual
extension by zero; the conclusion concerns the original restricted spatial map. -/
theorem componentMap_quasiIso (f : C(X, Y)) (x : X) (y : Y)
    (hpre : ∀ z, f z ∈ pathComponent y ↔ z ∈ pathComponent x)
    (hf : ∀ B : System.{u, u} Y, QuasiIso (pushforwardChainMap f B))
    (A : System.{u, u} (pathComponent y)) :
    QuasiIso (pushforwardChainMap (componentMap f x y hpre) A) := by
  let B := componentExtension y A
  let j := subspaceInclusion (pathComponent x)
  let k := subspaceInclusion (pathComponent y)
  let a := componentMap f x y hpre
  have hj : IsIso (pushforwardChainMap j (pullback f B)) := by
    apply pathComponentInclusion_pushforwardChainMap_isIso_of_support
    intro z hz
    exact componentExtension_isZero_off y A (f z) (fun h ↦ hz ((hpre z).mp h))
  have hk : IsIso (pushforwardChainMap k B) :=
    pathComponentInclusion_pushforwardChainMap_isIso_of_support y B
      (componentExtension_isZero_off y A)
  have hfB := hf B
  let e := pullbackSquareIso j k a f (componentMap_square f x y hpre) B
  have he : QuasiIso (coefficientChainMap e.hom) := by
    change QuasiIso (coefficientChainIso e).hom
    infer_instance
  have hcomp : QuasiIso
      ((coefficientChainMap e.hom ≫ pushforwardChainMap a (pullback k B)) ≫
        pushforwardChainMap k B) := by
    rw [Category.assoc]
    rw [pushforwardChainMap_square]
    infer_instance
  have hleft : QuasiIso
      (coefficientChainMap e.hom ≫ pushforwardChainMap a (pullback k B)) :=
    quasiIso_of_comp_right
      (coefficientChainMap e.hom ≫ pushforwardChainMap a (pullback k B))
      (pushforwardChainMap k B)
  have ha : QuasiIso (pushforwardChainMap a (pullback k B)) :=
    quasiIso_of_comp_left (coefficientChainMap e.hom) (pushforwardChainMap a (pullback k B))
  exact pushforwardChainMap_quasiIso_of_coefficientIso a
    (componentExtensionPullbackIso y A) ha

end FundamentalGroupoid.LocalCoefficients
