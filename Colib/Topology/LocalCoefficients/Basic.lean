/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Whiskering

/-!
Extracted from `Quillen/Topology/LocalCoefficients/Basic.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Definitions and proofs use the native
fundamental groupoid, simplicial modules, and Mathlib chain and homology functors.

# Local coefficient systems and actual path transport

A local coefficient system is a functor from the topological fundamental
groupoid to modules over the integers. Transport uses actual path homotopy
classes, so nontrivial monodromy is retained. This file constructs pullback
and the coefficient isomorphism induced by a specified homotopy. It makes
no homological invariance or plus-construction assumptions.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w

namespace FundamentalGroupoid.LocalCoefficients

/-- Integral local coefficient systems, including arbitrary monodromy. -/
abbrev System (X : Type u) [TopologicalSpace X] :=
  FundamentalGroupoid X ⥤ ModuleCat.{v} ℤ

variable {X : Type u} {Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]

/-- The coefficient module at a point. -/
abbrev fiber (A : System.{u, v} X) (x : X) : ModuleCat.{v} ℤ :=
  A.obj (FundamentalGroupoid.mk x)

/-- Transport along the homotopy class of an actual path. -/
def transport (A : System.{u, v} X) {x y : X} (p : Path x y) :
    fiber A x ⟶ fiber A y :=
  A.map (Path.Homotopic.Quotient.mk p)

@[simp]
theorem transport_refl (A : System.{u, v} X) (x : X) :
    transport A (Path.refl x) = 𝟙 (fiber A x) :=
  A.map_id _

/-- Concatenation is sent to composition, with no trivial-monodromy hypothesis. -/
@[reassoc]
theorem transport_trans (A : System.{u, v} X) {x y z : X}
    (p : Path x y) (q : Path y z) :
    transport A (p.trans q) = transport A p ≫ transport A q := by
  exact A.map_comp (Path.Homotopic.Quotient.mk p) (Path.Homotopic.Quotient.mk q)

/-- Endpoint-fixed homotopic paths induce the same transport. -/
theorem transport_eq_of_homotopic (A : System.{u, v} X) {x y : X}
    {p q : Path x y} (h : p.Homotopic q) : transport A p = transport A q :=
  congrArg A.map (Quotient.sound h)

/-- Reversing the path supplies the inverse transport. -/
def transportIso (A : System.{u, v} X) {x y : X} (p : Path x y) :
    fiber A x ≅ fiber A y where
  hom := transport A p
  inv := transport A p.symm
  hom_inv_id := by
    rw [← transport_trans, transport_eq_of_homotopic A (Path.Homotopic.trans_symm p),
      transport_refl]
  inv_hom_id := by
    rw [← transport_trans, transport_eq_of_homotopic A (Path.Homotopic.symm_trans p),
      transport_refl]

/-- Pullback along a continuous map, as precomposition on fundamental groupoids. -/
def pullback (f : C(X, Y)) (A : System.{w, v} Y) : System.{u, v} X :=
  FundamentalGroupoid.map f ⋙ A

@[simp]
theorem pullback_fiber (f : C(X, Y)) (A : System.{w, v} Y) (x : X) :
    fiber (pullback f A) x = fiber A (f x) := rfl

@[simp]
theorem pullback_transport (f : C(X, Y)) (A : System.{w, v} Y)
    {x y : X} (p : Path x y) :
    transport (pullback f A) p = transport A (p.map f.continuous) := rfl

/-- A specified homotopy determines the required coefficient isomorphism.
It is not replaced by equality of the underlying continuous maps. -/
def homotopyPullbackIso {f g : C(X, Y)} (H : f.Homotopy g)
    (A : System.{w, v} Y) : pullback f A ≅ pullback g A :=
  Functor.isoWhiskerRight (asIso (FundamentalGroupoidFunctor.homotopicMapsNatIso H)) A

@[simp]
theorem homotopyPullbackIso_hom_app {f g : C(X, Y)} (H : f.Homotopy g)
    (A : System.{w, v} Y) (x : X) :
    (homotopyPullbackIso H A).hom.app (FundamentalGroupoid.mk x) =
      transport A (H.evalAt x) := rfl

/-- Maps of local systems commute with path transport. -/
@[reassoc]
theorem transport_naturality {A B : System.{u, v} X} (η : A ⟶ B)
    {x y : X} (p : Path x y) :
    transport A p ≫ η.app (FundamentalGroupoid.mk y) =
      η.app (FundamentalGroupoid.mk x) ≫ transport B p :=
  η.naturality (Path.Homotopic.Quotient.mk p)

/-- The constant coefficient system used for comparison with ordinary homology. -/
def constant (X : Type u) [TopologicalSpace X] (V : ModuleCat.{v} ℤ) : System.{u, v} X :=
  (Functor.const (FundamentalGroupoid X)).obj V

@[simp]
theorem constant_transport (V : ModuleCat.{v} ℤ) {x y : X} (p : Path x y) :
    transport (constant X V) p = 𝟙 V := rfl

end FundamentalGroupoid.LocalCoefficients
