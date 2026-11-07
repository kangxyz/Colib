/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Fundamental groups of path components

The inclusion of a path component induces an isomorphism on fundamental groups.
Paths lift by restricting their codomain, and endpoint-fixed homotopies lift by
the same construction on each intermediate path. The resulting equivalence has
exactly the original inclusion-induced homomorphism as its forward map.
In particular, commutativity of the ambient fundamental group restricts to the
component without changing either group's multiplication.
-/

/-! Implementation source: `Quillen/Topology/HomotopyGroups/PathComponent.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual maps, endpoint paths,
universes and signs are retained, with native Colib dependencies. -/
@[expose] public section

noncomputable section

universe u

namespace Topology

variable {X : Type u} [TopologicalSpace X] {x : X}

/-- Every point on a path starting in a component belongs to that component. -/
lemma path_mem_pathComponent {a b : X} (p : Path a b)
    (ha : a ∈ pathComponent x) (t : unitInterval) : p t ∈ pathComponent x := by
  have h : Joined a (p t) :=
    ⟨(p.truncateOfLE t.property.1).cast p.extend_zero.symm
      (p.extend_extends' t).symm⟩
  exact h.mem_pathComponent ha

/-- Restrict a path between points of one component to that component. -/
def pathComponentPath {a b : pathComponent x} (p : Path a.val b.val) : Path a b where
  toFun t := ⟨p t, path_mem_pathComponent p a.property t⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

@[simp]
lemma pathComponentPath_map {a b : pathComponent x} (p : Path a.val b.val) :
    (pathComponentPath p).map continuous_subtype_val = p := by
  ext t
  rfl

/-- An endpoint-fixed homotopy in the ambient space restricts to its component. -/
def pathComponentHomotopy {a b : pathComponent x} {p q : Path a b}
    (H : (p.map continuous_subtype_val).Homotopy (q.map continuous_subtype_val)) :
    p.Homotopy q where
  toFun t := ⟨H t, path_mem_pathComponent (H.eval t.1) a.property t.2⟩
  continuous_toFun := H.continuous.subtype_mk _
  map_zero_left t := Subtype.ext (H.apply_zero t)
  map_one_left t := Subtype.ext (H.apply_one t)
  prop' t _s hs := Subtype.ext (H.eq_fst t hs)

/-- The actual fundamental-group map induced by component inclusion is bijective. -/
theorem fundamentalGroup_map_pathComponent_bijective (x : X) :
    Function.Bijective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(pathComponent x, X))
      ⟨x, mem_pathComponent_self x⟩) := by
  constructor
  · intro a b h
    rcases a with ⟨a⟩
    induction a using Path.Homotopic.Quotient.ind with | mk p =>
    rcases b with ⟨b⟩
    induction b using Path.Homotopic.Quotient.ind with | mk q =>
    obtain ⟨H⟩ := Path.Homotopic.Quotient.exact (congrArg CategoryTheory.End.asHom h)
    exact congrArg FundamentalGroup.fromPath (Quotient.sound ⟨pathComponentHomotopy H⟩)
  · intro a
    rcases a with ⟨a⟩
    induction a using Path.Homotopic.Quotient.ind with | mk p =>
    let q := pathComponentPath (a := ⟨x, mem_pathComponent_self x⟩)
      (b := ⟨x, mem_pathComponent_self x⟩) p
    refine ⟨FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q), ?_⟩
    apply CategoryTheory.End.ext
    change Path.Homotopic.Quotient.mk
      (q.map continuous_subtype_val) = _
    dsimp [q]
    rw [pathComponentPath_map]

/-- Component inclusion as a multiplicative equivalence of actual fundamental groups. -/
def pathComponentFundamentalGroupEquiv (x : X) :
    FundamentalGroup (pathComponent x) ⟨x, mem_pathComponent_self x⟩ ≃*
      FundamentalGroup X x :=
  MulEquiv.ofBijective (FundamentalGroup.map
    (⟨Subtype.val, continuous_subtype_val⟩ : C(pathComponent x, X))
    ⟨x, mem_pathComponent_self x⟩) (fundamentalGroup_map_pathComponent_bijective x)

@[simp]
lemma pathComponentFundamentalGroupEquiv_apply (x : X)
    (a : FundamentalGroup (pathComponent x) ⟨x, mem_pathComponent_self x⟩) :
    pathComponentFundamentalGroupEquiv x a = FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(pathComponent x, X))
      ⟨x, mem_pathComponent_self x⟩ a := rfl

/-- Ambient commutativity restricts to the component's unchanged fundamental group. -/
theorem pathComponentFundamentalGroup_mul_comm (x : X)
    (h : ∀ a b : FundamentalGroup X x, a * b = b * a)
    (a b : FundamentalGroup (pathComponent x) ⟨x, mem_pathComponent_self x⟩) :
    a * b = b * a := by
  apply (pathComponentFundamentalGroupEquiv x).injective
  simpa only [map_mul] using h (pathComponentFundamentalGroupEquiv x a)
    (pathComponentFundamentalGroupEquiv x b)

/-- The same component comparison on mathlib's actual first homotopy groups. -/
def pathComponentPiOneEquiv (x : X) :
    HomotopyGroup.Pi 1 (pathComponent x) ⟨x, mem_pathComponent_self x⟩ ≃*
      HomotopyGroup.Pi 1 X x :=
  HomotopyGroup.pi1MulEquivFundamentalGroup.trans
    ((pathComponentFundamentalGroupEquiv x).trans
      HomotopyGroup.pi1MulEquivFundamentalGroup.symm)

/-- The first-homotopy-group comparison retains the original inclusion-induced map. -/
@[simp]
lemma pathComponentPiOneEquiv_fundamentalGroup (x : X)
    (a : HomotopyGroup.Pi 1 (pathComponent x) ⟨x, mem_pathComponent_self x⟩) :
    HomotopyGroup.pi1MulEquivFundamentalGroup (pathComponentPiOneEquiv x a) =
      FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(pathComponent x, X))
        ⟨x, mem_pathComponent_self x⟩
        (HomotopyGroup.pi1MulEquivFundamentalGroup a) := by
  exact HomotopyGroup.pi1MulEquivFundamentalGroup.apply_symm_apply _

/-- Ambient commutativity restricts to the component's unchanged first homotopy group. -/
theorem pathComponentPiOne_mul_comm (x : X)
    (h : ∀ a b : HomotopyGroup.Pi 1 X x, a * b = b * a)
    (a b : HomotopyGroup.Pi 1 (pathComponent x) ⟨x, mem_pathComponent_self x⟩) :
    a * b = b * a := by
  apply (pathComponentPiOneEquiv x).injective
  simpa only [map_mul] using h (pathComponentPiOneEquiv x a) (pathComponentPiOneEquiv x b)

end Topology
