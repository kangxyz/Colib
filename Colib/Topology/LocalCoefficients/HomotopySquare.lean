/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.HomotopyEquivalence

/-!
Adapted from the same-named Quillen source at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using the actual native chain
and homology maps with their coefficient identifications.
 # Actual local homology maps in a homotopy-commutative square -/

@[expose] public section
noncomputable section
open CategoryTheory
open scoped ContinuousMap
universe u
namespace FundamentalGroupoid.LocalCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y X' Y' : Type u}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']

/-- Transport a fixed target-system homology isomorphism across actual homotopy
 equivalences, retaining the original map on the opposite side of the square. -/
theorem isIso_pushforwardHomologyMap_of_homotopySquare
    (eX : X ≃ₕ X') (eY : Y ≃ₕ Y') (f : C(X, Y)) (g : C(X', Y'))
    (H : (g.comp eX.toFun).Homotopy (eY.toFun.comp f))
    (A : System.{u, u} Y') (n : ℕ)
    (hf : IsIso (pushforwardHomologyMap f (pullback eY.toFun A) n)) :
    IsIso (pushforwardHomologyMap g A n) := by
  have : IsIso (pushforwardHomologyMap eY.toFun A n) :=
    isIso_pushforwardHomologyMap_of_homotopyEquiv eY A n
  have : IsIso (pushforwardHomologyMap eX.toFun (pullback g A) n) :=
    isIso_pushforwardHomologyMap_of_homotopyEquiv eX (pullback g A) n
  have hfg : IsIso (pushforwardHomologyMap (eY.toFun.comp f) A n) := by
    rw [pushforwardHomologyMap_comp]
    change IsIso ((coefficientHomologyIso (pullbackCompositionIso f eY.toFun A) n).hom ≫ _)
    infer_instance
  have hg := (isIso_pushforwardHomologyMap_iff_of_homotopy H A n).mpr hfg
  rw [pushforwardHomologyMap_comp] at hg
  change IsIso ((coefficientHomologyIso (pullbackCompositionIso eX.toFun g A) n).hom ≫
    pushforwardHomologyMap eX.toFun (pullback g A) n ≫ pushforwardHomologyMap g A n) at hg
  exact (isIso_comp_left_iff _ _).mp ((isIso_comp_left_iff _ _).mp hg)

end FundamentalGroupoid.LocalCoefficients
