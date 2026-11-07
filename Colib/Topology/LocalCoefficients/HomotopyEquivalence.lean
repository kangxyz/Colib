/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.HomotopyInvariance

/-!
Adapted from `Quillen/Topology/LocalCoefficients/HomotopyEquivalence.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using the pinned native singular
simplices, module coproducts, and chain/homology functors.

# Homotopy equivalences preserve local-coefficient homology

A homotopy right inverse gives an epimorphism on homology with every target
local system. Using both homotopies then proves the original map is an
isomorphism; no compatibility between the two chosen homotopies is assumed.
-/

@[expose] public section

open CategoryTheory
open scoped ContinuousMap

noncomputable section

universe u

namespace FundamentalGroupoid.LocalCoefficients

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The actual identity-induced map is an isomorphism. -/
lemma isIso_pushforwardHomologyMap_id (A : System.{u, u} X) (n : ℕ) :
    IsIso (pushforwardHomologyMap (ContinuousMap.id X) A n) := by
  rw [pushforwardHomologyMap_id]
  change IsIso (coefficientHomologyIso (pullbackIdentityIso A) n).hom
  infer_instance

/-- A homotopy right inverse makes the original homology map an epimorphism. -/
lemma epi_pushforwardHomologyMap_of_right_homotopyInverse (f : C(X, Y)) (g : C(Y, X))
    (H : (f.comp g).Homotopy (ContinuousMap.id Y)) (A : System.{u, u} Y) (n : ℕ) :
    Epi (pushforwardHomologyMap f A n) := by
  have : IsIso (pushforwardHomologyMap (f.comp g) A n) :=
    (isIso_pushforwardHomologyMap_iff_of_homotopy H A n).mpr
      (isIso_pushforwardHomologyMap_id A n)
  apply epi_of_epi_fac (h := pushforwardHomologyMap (f.comp g) A n)
  exact (Category.assoc _ _ _).trans (pushforwardHomologyMap_comp g f A n).symm

/-- Every homotopy equivalence preserves arbitrary target local coefficients. -/
theorem isIso_pushforwardHomologyMap_of_homotopyEquiv (e : X ≃ₕ Y) (A : System.{u, u} Y) (n : ℕ) :
    IsIso (pushforwardHomologyMap e.toFun A n) := by
  let a := coefficientHomologyIso (pullbackCompositionIso e.invFun e.toFun A) n
  let b := pushforwardHomologyMap e.invFun (pullback e.toFun A) n
  let c := pushforwardHomologyMap e.toFun A n
  have : Epi b :=
    epi_pushforwardHomologyMap_of_right_homotopyInverse e.invFun e.toFun e.left_inv.some _ n
  have : IsIso (pushforwardHomologyMap (e.toFun.comp e.invFun) A n) :=
    (isIso_pushforwardHomologyMap_iff_of_homotopy e.right_inv.some A n).mpr
      (isIso_pushforwardHomologyMap_id A n)
  have h : a.hom ≫ (b ≫ c) = pushforwardHomologyMap (e.toFun.comp e.invFun) A n :=
    (pushforwardHomologyMap_comp e.invFun e.toFun A n).symm
  have : IsIso (b ≫ c) := IsIso.of_isIso_fac_left h
  have : Mono b := mono_of_mono b c
  have : IsIso b := isIso_of_mono_of_epi b
  exact IsIso.of_isIso_comp_left b c

/-- The homology isomorphism retains the actual map of the homotopy equivalence. -/
def homologyIsoOfHomotopyEquiv (e : X ≃ₕ Y) (A : System.{u, u} Y) (n : ℕ) :
    homology (pullback e.toFun A) n ≅ homology A n := by
  have := isIso_pushforwardHomologyMap_of_homotopyEquiv e A n
  exact asIso (pushforwardHomologyMap e.toFun A n)

@[simp]
theorem homologyIsoOfHomotopyEquiv_hom (e : X ≃ₕ Y) (A : System.{u, u} Y) (n : ℕ) :
    (homologyIsoOfHomotopyEquiv e A n).hom = pushforwardHomologyMap e.toFun A n := rfl

end FundamentalGroupoid.LocalCoefficients
