/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.CategoryTheory.Whiskering

/-!
# Constant Functor

Killing all loops at a chosen base object makes chosen transports natural
on every actual groupoid arrow. This is the nontrivial overlap condition; mere
connectedness would only provide the arrows alpha.
-/

@[expose] public section

noncomputable section
open CategoryTheory
universe u v w z
namespace CategoryTheory

/-- Killing all loops at a chosen base object makes chosen transports natural
on every actual groupoid arrow. This is the nontrivial overlap condition; mere
connectedness would only provide the arrows alpha. -/
theorem transport_naturality_of_loop_trivial
    {D : Type u} [Groupoid.{v} D] {C : Type w} [Category.{z} C]
    (F : D ⥤ C) (b : D) (α : ∀ x : D, x ⟶ b)
    (hloop : ∀ f : b ⟶ b, F.map f = 𝟙 (F.obj b))
    {x y : D} (p : x ⟶ y) : F.map p ≫ F.map (α y) = F.map (α x) := by
  apply (cancel_epi (F.map (inv (α x)))).mp
  calc
    F.map (inv (α x)) ≫ (F.map p ≫ F.map (α y)) =
        F.map (inv (α x) ≫ p ≫ α y) := by simp
    _ = 𝟙 (F.obj b) := hloop _
    _ = F.map (inv (α x)) ≫ F.map (α x) := by simp

/-- A loop-trivial functor is naturally isomorphic to the constant functor via
specified actual base paths. The target need not itself be a groupoid. -/
def constantIsoOfLoopTrivial
    {D : Type u} [Groupoid.{v} D] {C : Type w} [Category.{z} C]
    (F : D ⥤ C) (b : D) (α : ∀ x : D, x ⟶ b)
    (hloop : ∀ f : b ⟶ b, F.map f = 𝟙 (F.obj b)) :
    F ≅ (Functor.const D).obj (F.obj b) :=
  NatIso.ofComponents (fun x => F.mapIso (asIso (α x))) (by
    intro x y p
    simpa using transport_naturality_of_loop_trivial F b α hloop p)

end CategoryTheory
