/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Homotopy.HomotopyGroup.BasedHomotopy

/-! # Based homotopy composition and cancellation by an actual forward map

Implementation provenance: `Quillen/Waldhausen/Additivity/BasedHomotopyTools.lean`
at commit c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps, hypotheses and
universes are retained; no subdivision realization equivalence is assumed.
-/
@[expose] public section


noncomputable section
open scoped Topology unitInterval

namespace CategoryTheory.Waldhausen.Additivity

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- An explicitly constant vertex track gives an actual relative homotopy. -/
def homotopyRelOfFixed {f g : C(X, Y)} (H : f.Homotopy g) (x : X) (y : Y)
    (h : ∀ t, H (t, x) = y) : f.HomotopyRel g {x} where
  toHomotopy := H
  prop' t z hz := by
    have hz' := Set.mem_singleton_iff.mp hz
    subst z
    exact (h t).trans ((h 0).symm.trans (H.apply_zero x))

/-- Precomposition of a relative homotopy requires only basedness of the
actual forward continuous map, never any property of an inverse. -/
def homotopyRelPrecompPoint {f g : C(Y, Z)} {y : Y}
    (H : f.HomotopyRel g {y}) (e : C(X, Y)) (x : X) (he : e x = y) :
    (f.comp e).HomotopyRel (g.comp e) {x} where
  toHomotopy := H.toHomotopy.compContinuousMap e
  prop' t z hz := by
    have hz' := Set.mem_singleton_iff.mp hz
    subst z
    change H (t, e x) = f (e x)
    rw [he]
    exact H.eq_fst t (Set.mem_singleton y)

/-- A based homotopy after an actual based map detects equality of induced
homomorphisms when that forward map is surjective on the relevant group. -/
theorem piMap_eq_of_based_precomp_surjective (n : ℕ)
    {x : X} {y : Y} {z : Z} (e : C(X, Y)) (he : e x = y)
    (hes : Function.Surjective (HomotopyGroup.piMap n e he)) (f g : C(Y, Z))
    (hf : f y = z) (hg : g y = z)
    (H : (f.comp e).HomotopyRel (g.comp e) {x}) :
    HomotopyGroup.piMap n f hf = HomotopyGroup.piMap n g hg := by
  have hp := HomotopyGroup.piMap_eq_of_based_homotopy (x := x) (y := z) (f := f.comp e)
    (g := g.comp e) n
    ((congrArg f he).trans hf) ((congrArg g he).trans hg) H.toHomotopy
    (fun t ↦ (H.eq_fst t (Set.mem_singleton x)).trans ((congrArg f he).trans hf))
  have hp' : (HomotopyGroup.piMap n f hf).comp (HomotopyGroup.piMap n e he) =
    (HomotopyGroup.piMap n g hg).comp (HomotopyGroup.piMap n e he) :=
    (HomotopyGroup.mapHom_comp (N := Fin (n + 1)) e he f hf).symm.trans
      (hp.trans (HomotopyGroup.mapHom_comp (N := Fin (n + 1)) e he g hg))
  ext q
  obtain ⟨p, rfl⟩ := hes q
  exact DFunLike.congr_fun hp' p

end CategoryTheory.Waldhausen.Additivity
