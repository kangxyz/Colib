/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.Homotopy.HomotopyGroup.Map

/-!
# Based homotopy invariance of the actual homotopy-group maps

Postcomposition with a homotopy fixed at the basepoint gives a homotopy of
Mathlib generalized loops relative to the entire cube boundary. Passing to the
existing homotopy quotient identifies the induced maps and homomorphisms.

## Implementation provenance

The four based-homotopy declarations are extracted from
`Quillen/Topology/HomotopyGroups/Map.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Independent loop-index, source and target
universes, the specified basepoint equations and the actual quotient maps are
retained. Only names and lower imports change.
-/

@[expose] public noncomputable section

open scoped Topology unitInterval

universe w v u

variable {N : Type w} {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

/-- A based homotopy of maps gives a homotopy of their postcomposed
loops relative to the entire cube boundary. -/
def GenLoop.postcompHomotopy {f g : C(X, Y)} (hf : f x = y) (hg : g x = y)
    (H : f.Homotopy g) (hH : ∀ t, H (t, x) = y) (p : GenLoop N X x) :
    (GenLoop.postcomp f hf p).val.HomotopyRel (GenLoop.postcomp g hg p).val
      (Cube.boundary N) where
  toHomotopy := H.compContinuousMap p.val
  prop' t z hz := by
    change H (t, p z) = f (p z)
    rw [GenLoop.boundary p z hz, hH t, hf]

/-- Based homotopic continuous maps induce equal maps on the homotopy set. -/
theorem HomotopyGroup.map_eq_of_based_homotopy {f g : C(X, Y)}
    (hf : f x = y) (hg : g x = y)
    (H : f.Homotopy g) (hH : ∀ t, H (t, x) = y) :
    HomotopyGroup.map (N := N) f hf = HomotopyGroup.map g hg := by
  funext a
  refine Quotient.inductionOn a (fun p => ?_)
  exact Quotient.sound ⟨GenLoop.postcompHomotopy hf hg H hH p⟩

/-- Based homotopic continuous maps induce equal homotopy-group homomorphisms. -/
theorem HomotopyGroup.mapHom_eq_of_based_homotopy [DecidableEq N] [Nonempty N]
    {f g : C(X, Y)} (hf : f x = y) (hg : g x = y)
    (H : f.Homotopy g) (hH : ∀ t, H (t, x) = y) :
    HomotopyGroup.mapHom (N := N) f hf = HomotopyGroup.mapHom g hg := by
  ext a
  exact congrFun (HomotopyGroup.map_eq_of_based_homotopy hf hg H hH) a

/-- Based homotopic continuous maps induce equal maps on `π_(n+1)`. -/
theorem HomotopyGroup.piMap_eq_of_based_homotopy (n : ℕ) {f g : C(X, Y)}
    (hf : f x = y) (hg : g x = y)
    (H : f.Homotopy g) (hH : ∀ t, H (t, x) = y) :
    HomotopyGroup.piMap n f hf = HomotopyGroup.piMap n g hg :=
  HomotopyGroup.mapHom_eq_of_based_homotopy hf hg H hH


attribute [colib_tag "COL-0071",
  colib_ref "HatcherAT" "Section 4.1, functoriality and based homotopy paragraph, page 342"
    "generalization" "Based homotopy invariance extended to the stated generalized-loop indices"]
  GenLoop.postcompHomotopy
  HomotopyGroup.map_eq_of_based_homotopy
  HomotopyGroup.mapHom_eq_of_based_homotopy

attribute [colib_tag "COL-0071",
  colib_ref "HatcherAT" "Section 4.1, functoriality and based homotopy paragraph, page 342"
    "adaptation" "Based homotopic maps induce equal homomorphisms in degree n + 1"]
  HomotopyGroup.piMap_eq_of_based_homotopy
