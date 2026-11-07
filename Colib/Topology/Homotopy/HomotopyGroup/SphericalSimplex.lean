/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.Cube.StickBreaking

/-! # Boundary-constant native singular simplices

The actual domain is the pinned native standard simplex. The ordered cube
quotient in the next file, rather than a chosen homeomorphism, relates these
representatives and their relative homotopies to the actual homotopy groups.

Extracted from `Quillen/Topology/HomotopyGroups/SphericalSimplex.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Only the original representative
subtype and its elementary API are needed for the normalized cap descent.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open scoped Topology unitInterval

universe u

namespace Topology

/-- A singular simplex sending its entire geometric boundary to the basepoint. -/
def SphericalSimplex (Z : Type u) [TopologicalSpace Z] (z : Z) (n : ℕ) :=
  {f : C(_root_.stdSimplex ℝ (Fin (n + 1)), Z) // ∀ x ∈ stdSimplex.boundary n, f x = z}

namespace SphericalSimplex

variable {Z : Type u} [TopologicalSpace Z] {z : Z} {n : ℕ}

instance : FunLike (SphericalSimplex Z z n) (_root_.stdSimplex ℝ (Fin (n + 1))) Z where
  coe f := f.val
  coe_injective := fun ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ h ↦ by congr

@[simp] theorem coe_val (f : SphericalSimplex Z z n) : ⇑f.val = f := rfl

@[ext] theorem ext {f g : SphericalSimplex Z z n} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.coe_injective (funext h)

@[simp] theorem boundary (f : SphericalSimplex Z z n)
    (x : _root_.stdSimplex ℝ (Fin (n + 1))) (hx : x ∈ stdSimplex.boundary n) : f x = z :=
  f.property x hx

/-- The constant singular simplex. -/
def const : SphericalSimplex Z z n := ⟨ContinuousMap.const _ z, fun _ _ ↦ rfl⟩

@[simp] theorem const_apply (x : _root_.stdSimplex ℝ (Fin (n + 1))) :
    (const : SphericalSimplex Z z n) x = z := rfl

end SphericalSimplex
end Topology
