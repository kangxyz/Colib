/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Prespectrum.StableHomotopy
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
Stable equivalences are isomorphisms on all actual integer-graded stable homotopy groups.
Identities, composition, and levelwise complete weak equivalences satisfy this predicate. No
triangulated or localized spectrum category is asserted.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/StableEquivalence.lean` at
Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual native prespectrum,
integer degrees, original structure maps, coefficients and signs are retained. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u
namespace Topology.LoopPrespectrum

/-- A morphism inducing isomorphisms on every integer-graded stable homotopy group. -/
def IsStableEquivalence {E F : LoopPrespectrum.{u}} (f : E ⟶ F) : Prop :=
  ∀ d : ℤ, IsIso ((stableHomotopyFunctor d).map f)

lemma IsStableEquivalence.id (E : LoopPrespectrum.{u}) : IsStableEquivalence (𝟙 E) := by
  intro d
  infer_instance

lemma IsStableEquivalence.comp {E F G : LoopPrespectrum.{u}} {f : E ⟶ F} {g : F ⟶ G}
    (hf : IsStableEquivalence f) (hg : IsStableEquivalence g) : IsStableEquivalence (f ≫ g) := by
  intro d
  rw [Functor.map_comp]
  have := hf d
  have := hg d
  infer_instance

lemma isStableEquivalence_of_levelwise {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (hf : ∀ n, IsWeakHomotopyEquivalence (f.map n)) : IsStableEquivalence f := by
  intro d
  have hstage (n : ℕ) : IsIso ((stableSystemMap f d).app n) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    have hb {y : F.space ((-d).toNat+n+2)}
        (h : f.map ((-d).toNat+n+2) (E.point ((-d).toNat+n+2)) = y) :
        Function.Bijective (HomotopyGroup.map (N := Fin (d.toNat+n+2))
          (f.map ((-d).toNat+n+2)) h) := by
      cases h
      exact (hf ((-d).toNat+n+2)).homotopy_bijective (E.point ((-d).toNat+n+2)) (d.toNat+n+2)
    exact hb (f.map_point ((-d).toNat+n+2))
  let : ∀ n, IsIso ((stableSystemMap f d).app n) := hstage
  let : IsIso (stableSystemMap f d) := NatIso.isIso_of_isIso_app _
  change IsIso (colim.map (stableSystemMap f d))
  infer_instance

end Topology.LoopPrespectrum
