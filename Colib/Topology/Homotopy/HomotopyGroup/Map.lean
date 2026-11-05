/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Maps of generalized-loop homotopy groups

These maps act on Mathlib's actual `GenLoop` and `HomotopyGroup` quotients.
Multiplication uses the existing `mul_spec`: the representatives multiply
by concatenating `q` before `p`. No new group realization is introduced.

## Implementation provenance

Extracted from `Quillen/Topology/HomotopyGroups/Map.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The source maps, basepoints,
universes and degree shift are retained. Only ownership and lower imports change.
-/

@[expose] public noncomputable section

open scoped Topology unitInterval

universe w v u

variable {N : Type w} {X : Type u} {Y : Type v} {Z : Type*}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {x : X} {y : Y} {z : Z}

/-- Postcomposition of a generalized loop by a pointed continuous map. -/
def GenLoop.postcomp (f : C(X, Y)) (h : f x = y) (p : GenLoop N X x) :
    GenLoop N Y y :=
  ⟨f.comp p.val, fun t ht => (congrArg f (p.property t ht)).trans h⟩

@[simp]
theorem GenLoop.postcomp_apply (f : C(X, Y)) (h : f x = y)
    (p : GenLoop N X x) (t : N → unitInterval) :
    GenLoop.postcomp f h p t = f (p t) := rfl

/-- Postcomposition respects homotopies fixed on the cube boundary. -/
theorem GenLoop.postcomp_homotopic (f : C(X, Y)) (h : f x = y)
    {p q : GenLoop N X x} (H : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (GenLoop.postcomp f h p) (GenLoop.postcomp f h q) :=
  ContinuousMap.HomotopicRel.comp_continuousMap H f

@[simp]
theorem GenLoop.postcomp_const (f : C(X, Y)) (h : f x = y) :
    GenLoop.postcomp (N := N) f h GenLoop.const = GenLoop.const := by
  ext t
  exact h

/-- Postcomposition commutes with concatenation in every cube direction. -/
@[simp]
theorem GenLoop.postcomp_transAt [DecidableEq N] (f : C(X, Y)) (h : f x = y)
    (i : N) (p q : GenLoop N X x) :
    GenLoop.postcomp f h (GenLoop.transAt i p q) =
      GenLoop.transAt i (GenLoop.postcomp f h p) (GenLoop.postcomp f h q) := by
  ext t
  simp only [GenLoop.postcomp_apply, GenLoop.transAt, GenLoop.coe_copy]
  split_ifs <;> rfl

/-- The map on the homotopy quotient induced by a pointed continuous map.
This also makes sense for the zeroth homotopy set. -/
def HomotopyGroup.map (f : C(X, Y)) (h : f x = y) :
    HomotopyGroup N X x → HomotopyGroup N Y y :=
  Quotient.map (GenLoop.postcomp f h) (fun _ _ H => GenLoop.postcomp_homotopic f h H)

@[simp]
theorem HomotopyGroup.map_mk (f : C(X, Y)) (h : f x = y) (p : GenLoop N X x) :
    HomotopyGroup.map f h (Quotient.mk' p) = Quotient.mk' (GenLoop.postcomp f h p) := rfl

/-- On positive-dimensional homotopy groups, the induced map is a group
homomorphism. Multiplication is the existing mathlib group multiplication. -/
def HomotopyGroup.mapHom [DecidableEq N] [Nonempty N] (f : C(X, Y)) (h : f x = y) :
    HomotopyGroup N X x →* HomotopyGroup N Y y where
  toFun := HomotopyGroup.map f h
  map_one' := by
    change Quotient.mk' (GenLoop.postcomp f h GenLoop.const) = Quotient.mk' GenLoop.const
    rw [GenLoop.postcomp_const]
  map_mul' a b := by
    refine Quotient.inductionOn₂ a b (fun p q => ?_)
    simp only [HomotopyGroup.mul_spec (i := Classical.arbitrary N)]
    exact (congrArg Quotient.mk' (GenLoop.postcomp_transAt f h _ q p)).trans
      (HomotopyGroup.mul_spec (i := Classical.arbitrary N)).symm

@[simp]
theorem HomotopyGroup.map_id (a : HomotopyGroup N X x) :
    HomotopyGroup.map (ContinuousMap.id X) rfl a = a := by
  refine Quotient.inductionOn a (fun p => ?_)
  apply congrArg Quotient.mk'
  ext t
  rfl

@[simp]
theorem HomotopyGroup.map_comp (f : C(X, Y)) (hf : f x = y)
    (g : C(Y, Z)) (hg : g y = z) (a : HomotopyGroup N X x) :
    HomotopyGroup.map (g.comp f) ((congrArg g hf).trans hg) a =
      HomotopyGroup.map g hg (HomotopyGroup.map f hf a) := by
  refine Quotient.inductionOn a (fun p => ?_)
  rfl

@[simp]
theorem HomotopyGroup.mapHom_apply [DecidableEq N] [Nonempty N]
    (f : C(X, Y)) (h : f x = y) (a : HomotopyGroup N X x) :
    HomotopyGroup.mapHom f h a = HomotopyGroup.map f h a := rfl

@[simp]
theorem HomotopyGroup.mapHom_id [DecidableEq N] [Nonempty N] :
    HomotopyGroup.mapHom (N := N) (x := x) (ContinuousMap.id X) rfl =
      MonoidHom.id (HomotopyGroup N X x) := by
  ext a
  exact HomotopyGroup.map_id a

@[simp]
theorem HomotopyGroup.mapHom_comp [DecidableEq N] [Nonempty N]
    (f : C(X, Y)) (hf : f x = y) (g : C(Y, Z)) (hg : g y = z) :
    HomotopyGroup.mapHom (N := N) (g.comp f) ((congrArg g hf).trans hg) =
      (HomotopyGroup.mapHom g hg).comp (HomotopyGroup.mapHom f hf) := by
  ext a
  exact HomotopyGroup.map_comp f hf g hg a

/-- The induced homomorphism on the actual `(n + 1)`st homotopy group. -/
abbrev HomotopyGroup.piMap (n : ℕ) (f : C(X, Y)) (h : f x = y) :
    HomotopyGroup.Pi (n + 1) X x →* HomotopyGroup.Pi (n + 1) Y y :=
  HomotopyGroup.mapHom f h

attribute [colib_tag "COL-0052",
  colib_ref "HatcherAT"
    "Section 4.1, p. 342, functoriality of homotopy groups" "adaptation"
    "Postcomposition on the actual homotopy quotient using its existing multiplication"]
  HomotopyGroup.mapHom
  HomotopyGroup.piMap
  HomotopyGroup.mapHom_id
  HomotopyGroup.mapHom_comp
