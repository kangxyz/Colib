/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.Homotopy.Basic

/-!
# An actual local connector and its relative homotopies

This interface contains only geometric data: an open diagonal neighborhood
and a continuous, diagonal-fixed connector. In particular it contains no
realization, domination maps, CW assertion, or extension certificate.
-/

/-! Implementation source: `Quillen/Topology/LocalEquiconnection.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual topologies,
path classes, dependent endpoint equalities and covering maps are retained. -/
@[expose] public section
noncomputable section
open scoped Topology unitInterval
universe u v
namespace Topology

/-- A continuous connector on an open neighborhood of the whole diagonal. -/
structure LocalEquiconnection (A : Type u) [TopologicalSpace A] where
  /-- Pairs on which the connector is defined. -/
  domain : Set (A × A)
  /-- The connector domain is open in the original product topology. -/
  isOpen_domain : IsOpen domain
  /-- Every diagonal pair lies in the domain. -/
  diagonal_mem : ∀ x, (x, x) ∈ domain
  /-- The actual continuous connector, with interval last. -/
  connector : C(domain × I, A)
  /-- Initial endpoint. -/
  connector_zero : ∀ p : domain, connector (p, 0) = p.1.1
  /-- Terminal endpoint. -/
  connector_one : ∀ p : domain, connector (p, 1) = p.1.2
  /-- Every point of the whole diagonal is fixed at every time. -/
  connector_diagonal : ∀ x t, connector (⟨(x, x), diagonal_mem x⟩, t) = x

namespace LocalEquiconnection
variable {A : Type u} [TopologicalSpace A] (E : LocalEquiconnection A)

/-- Convexity for the specified connector includes its domain condition. -/
structure IsConvex (V : Set A) : Prop where
  /-- Every ordered pair in the set belongs to the domain. -/
  pair_mem : ∀ ⦃x y⦄, x ∈ V → y ∈ V → (x, y) ∈ E.domain
  /-- Interpolation stays in the same set. -/
  connector_mem : ∀ ⦃x y⦄ (hx : x ∈ V) (hy : y ∈ V) (t : I),
    E.connector (⟨(x, y), pair_mem hx hy⟩, t) ∈ V

/-- Connector-convex sets are stable under intersections. -/
theorem IsConvex.inter {V W : Set A} (hV : E.IsConvex V) (hW : E.IsConvex W) :
    E.IsConvex (V ∩ W) where
  pair_mem {_x _y} hx hy := hV.pair_mem hx.1 hy.1
  connector_mem {_x _y} hx hy t := ⟨hV.connector_mem hx.1 hy.1 t,
    hW.connector_mem hx.2 hy.2 t⟩

variable {X : Type v} [TopologicalSpace X]

/-- The actual connector applied to two pointwise-close continuous maps. -/
def closeHomotopy (f g : C(X, A)) (h : ∀ x, (f x, g x) ∈ E.domain) :
    f.Homotopy g where
  toFun p := E.connector (⟨(f p.2, g p.2), h p.2⟩, p.1)
  continuous_toFun := E.connector.continuous.comp
    (((f.continuous.comp continuous_snd).prodMk
      (g.continuous.comp continuous_snd)).subtype_mk _ |>.prodMk continuous_fst)
  map_zero_left x := E.connector_zero ⟨(f x, g x), h x⟩
  map_one_left x := E.connector_one ⟨(f x, g x), h x⟩

/-- The displayed close-map homotopy fixes the full equality locus. -/
theorem closeHomotopy_eq_of_eq (f g : C(X, A))
    (h : ∀ x, (f x, g x) ∈ E.domain) (x : X) (hx : f x = g x) (t : I) :
    E.closeHomotopy f g h (t, x) = f x := by
  change E.connector (⟨(f x, g x), h x⟩, t) = f x
  simpa only [← hx] using E.connector_diagonal (f x) t

/-- Equality on any specified subset makes the constructed homotopy relative. -/
def closeHomotopyRel (f g : C(X, A)) (h : ∀ x, (f x, g x) ∈ E.domain)
    (S : Set X) (hS : ∀ x ∈ S, f x = g x) : f.HomotopyRel g S where
  toHomotopy := E.closeHomotopy f g h
  prop' t x hx := E.closeHomotopy_eq_of_eq f g h x (hS x hx) t

/-- A convex carrier supplies the domain condition without assuming a homotopy. -/
def carrierHomotopy (f g : C(X, A))
    (h : ∀ x, ∃ V, E.IsConvex V ∧ f x ∈ V ∧ g x ∈ V) : f.Homotopy g :=
  E.closeHomotopy f g fun x ↦ by
    obtain ⟨V, hV, hf, hg⟩ := h x
    exact hV.pair_mem hf hg

end LocalEquiconnection
end Topology
