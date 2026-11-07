/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.FiniteGrothendieckTelescope
public import Colib.Topology.LocalCoefficients.HomotopyEquivalence

/-!
Adapted from `Quillen/Topology/LocalCoefficients/FiniteTelescope.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original categorical maps.


# Actual local homology maps of finite categorical telescopes

The genuine terminal-fiber homotopy equivalence gives isomorphisms for every
target local system. Both the projection and final-stage inclusion retain their
original spatial maps. Infinite telescope and ordinary/fat realization model
comparisons remain separate.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace FundamentalGroupoid.LocalCoefficients

variable (F : ℕ ⥤ Cat.{u, u}) (n : ℕ)

/-- The original finite-model projection is an isomorphism on all target local homology. -/
theorem finiteTelescopeProjection_isIso
    (A : System.{u, u} (ClassifyingSpace (F.obj n))) (k : ℕ) :
    IsIso (pushforwardHomologyMap
      (classifyingSpaceMap (CategoryTheory.Grothendieck.FiniteTelescope.projection F n)).hom A k) :=
  isIso_pushforwardHomologyMap_of_homotopyEquiv
    (CategoryTheory.Grothendieck.FiniteTelescope.classifyingHomotopyEquiv F n) A k

/-- The original final-stage inclusion is an isomorphism for every local system
on the finite model itself, as needed for systems pulled back from an infinite model. -/
theorem finiteTelescopeLastInclusion_isIso
    (A : System.{u, u} (ClassifyingSpace (CategoryTheory.Grothendieck.FiniteTelescope.Model F n)))
    (k : ℕ) :
    IsIso (pushforwardHomologyMap
      (classifyingSpaceMap
        (CategoryTheory.Grothendieck.FiniteTelescope.inclusion F n (Fin.last n))).hom A k) :=
  isIso_pushforwardHomologyMap_of_homotopyEquiv
    (CategoryTheory.Grothendieck.FiniteTelescope.classifyingHomotopyEquiv F n).symm A k

end FundamentalGroupoid.LocalCoefficients
