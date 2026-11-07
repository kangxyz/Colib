/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Analysis.Convex.StdSimplex.BoundaryRetraction
public import Mathlib.Topology.Homotopy.Basic

/-! # Homotopy extension from the explicit simplex-boundary retraction

Closed-set gluing on the side-bottom union, followed by the explicit radial
retraction, gives homotopy extension with an arbitrary parameter space.
-/
@[expose] public section


noncomputable section

open scoped unitInterval

namespace stdSimplex

universe u v w

variable {X : Type u} {B : Type v} {Y : Type w}
  [TopologicalSpace X] [TopologicalSpace B] [TopologicalSpace Y]

/-- The side-bottom union associated to any subspace. -/
def closedCylinderUnion (S : Set B) : Set (B × I) :=
  {z | z.1 ∈ S ∨ z.2 = 0}

/-- Compatible initial and side data glued on the side-bottom union. -/
def closedCylinderGlueFun (S : Set B) (f : C(X × B, Y)) (H : C((X × S) × I, Y))
    (z : X × closedCylinderUnion S) : Y := by
  classical
  exact if hz : z.2.1.1 ∈ S then H ((z.1, ⟨z.2.1.1, hz⟩), z.2.1.2) else f (z.1, z.2.1.1)

lemma closedCylinderGlueFun_side (S : Set B) (f : C(X × B, Y))
    (H : C((X × S) × I, Y)) (x : X) (b : S) (t : I) :
    closedCylinderGlueFun S f H (x, ⟨(b.1, t), Or.inl b.2⟩) = H ((x, b), t) := by
  simp [closedCylinderGlueFun, b.2]

lemma closedCylinderGlueFun_bottom (S : Set B) (f : C(X × B, Y))
    (H : C((X × S) × I, Y)) (h : ∀ x b, H ((x, b), 0) = f (x, b.1))
    (x : X) (b : B) :
    closedCylinderGlueFun S f H (x, ⟨(b, 0), Or.inr rfl⟩) = f (x, b) := by
  classical
  by_cases hb : b ∈ S
  · simpa [closedCylinderGlueFun, hb] using h x ⟨b, hb⟩
  · simp [closedCylinderGlueFun, hb]

/-- The gluing map is continuous because its two pieces have closed domains. -/
theorem continuous_closedCylinderGlueFun (S : Set B) (hS : IsClosed S)
    (f : C(X × B, Y)) (H : C((X × S) × I, Y))
    (h : ∀ x b, H ((x, b), 0) = f (x, b.1)) :
    Continuous (closedCylinderGlueFun S f H) := by
  classical
  let A : Set (X × closedCylinderUnion S) := {z | z.2.1.1 ∈ S}
  let D : Set (X × closedCylinderUnion S) := {z | z.2.1.2 = 0}
  have hA : IsClosed A := hS.preimage (by fun_prop)
  have hD : IsClosed D := isClosed_eq (by fun_prop) continuous_const
  have hcover : A ∪ D = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    exact z.2.2
  rw [← continuousOn_univ, ← hcover]
  apply ContinuousOn.union_of_isClosed _ _ hA hD
  · rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous (fun z : A ↦
        H ((z.1.1, ⟨z.1.2.1.1, z.2⟩), z.1.2.1.2)) := by fun_prop
    convert hc using 1
    funext z
    have hz : z.1.2.1.1 ∈ S := z.2
    simp [closedCylinderGlueFun, hz]
  · rw [continuousOn_iff_continuous_domRestrict]
    have hc : Continuous (fun z : D ↦ f (z.1.1, z.1.2.1.1)) := by fun_prop
    convert hc using 1
    funext z
    have ht : z.1.2.1.2 = 0 := z.2
    simp only [Set.domRestrict_apply, closedCylinderGlueFun]
    split_ifs with hz
    · rw [ht]
      exact h _ _
    · rfl

/-- Bundled continuous closed-set gluing with arbitrary parameters. -/
def closedCylinderGlue (S : Set B) (hS : IsClosed S)
    (f : C(X × B, Y)) (H : C((X × S) × I, Y))
    (h : ∀ x b, H ((x, b), 0) = f (x, b.1)) : C(X × closedCylinderUnion S, Y) :=
  ⟨closedCylinderGlueFun S f H, continuous_closedCylinderGlueFun S hS f H h⟩

/-- Any continuous retraction onto the side-bottom union gives actual homotopy
extension, uniformly with respect to an arbitrary parameter space. -/
theorem exists_homotopy_extension_of_cylinder_retraction
    (S : Set B) (hS : IsClosed S) (r : C(B × I, closedCylinderUnion S))
    (hr : ∀ z : closedCylinderUnion S, r z.1 = z)
    (f : C(X × B, Y)) (H : C((X × S) × I, Y))
    (h : ∀ x b, H ((x, b), 0) = f (x, b.1)) :
    ∃ K : C((X × B) × I, Y),
      (∀ x b, K ((x, b), 0) = f (x, b)) ∧
      ∀ x (b : S) t, K ((x, b.1), t) = H ((x, b), t) := by
  let K : C((X × B) × I, Y) :=
    (closedCylinderGlue S hS f H h).comp
      ⟨fun z ↦ (z.1.1, r (z.1.2, z.2)), by fun_prop⟩
  refine ⟨K, ?_, ?_⟩
  · intro x b
    change closedCylinderGlueFun S f H (x, r (b, 0)) = f (x, b)
    rw [hr ⟨(b, 0), Or.inr rfl⟩]
    exact closedCylinderGlueFun_bottom S f H h x b
  · intro x b t
    change closedCylinderGlueFun S f H (x, r (b.1, t)) = H ((x, b), t)
    rw [hr ⟨(b.1, t), Or.inl b.2⟩]
    exact closedCylinderGlueFun_side S f H x b t

/-- The explicit homotopy extension operator for the geometric simplex boundary. -/
def simplexBoundaryHomotopyExtension (n : ℕ)
    (f : C(X × _root_.stdSimplex ℝ (Fin (n + 1)), Y))
    (H : C((X × boundary n) × I, Y))
    (h : ∀ x b, H ((x, b), 0) = f (x, b.1)) :
    C((X × _root_.stdSimplex ℝ (Fin (n + 1))) × I, Y) :=
  (closedCylinderGlue (boundary n) (isClosed_boundary n) f H h).comp
    ⟨fun z ↦ (z.1.1, simplexBoundaryCylinderRetraction n (z.1.2, z.2)), by fun_prop⟩

@[simp] theorem simplexBoundaryHomotopyExtension_zero (n : ℕ)
    (f : C(X × _root_.stdSimplex ℝ (Fin (n + 1)), Y))
    (H : C((X × boundary n) × I, Y))
    (h : ∀ x b, H ((x, b), 0) = f (x, b.1))
    (x : X) (b : _root_.stdSimplex ℝ (Fin (n + 1))) :
    simplexBoundaryHomotopyExtension n f H h ((x, b), 0) = f (x, b) := by
  change closedCylinderGlueFun (boundary n) f H
    (x, simplexBoundaryCylinderRetraction n (b, 0)) = f (x, b)
  rw [simplexBoundaryCylinderRetraction_coe n ⟨(b, 0), Or.inr rfl⟩]
  exact closedCylinderGlueFun_bottom _ f H h x b

@[simp] theorem simplexBoundaryHomotopyExtension_side (n : ℕ)
    (f : C(X × _root_.stdSimplex ℝ (Fin (n + 1)), Y))
    (H : C((X × boundary n) × I, Y))
    (h : ∀ x b, H ((x, b), 0) = f (x, b.1)) (x : X)
    (b : boundary n) (t : I) :
    simplexBoundaryHomotopyExtension n f H h ((x, b.1), t) = H ((x, b), t) := by
  change closedCylinderGlueFun (boundary n) f H
    (x, simplexBoundaryCylinderRetraction n (b.1, t)) = H ((x, b), t)
  rw [simplexBoundaryCylinderRetraction_coe n ⟨(b.1, t), Or.inl b.2⟩]
  exact closedCylinderGlueFun_side _ f H x b t

/-- The geometric simplex boundary has the homotopy extension property, also
after product with any parameter space. This is proved by the explicit radial
projection, rather than assumed as a cofibration hypothesis. -/
theorem simplexBoundary_homotopy_extension (n : ℕ)
    (f : C(X × _root_.stdSimplex ℝ (Fin (n + 1)), Y))
    (H : C((X × boundary n) × I, Y))
    (h : ∀ x b, H ((x, b), 0) = f (x, b.1)) :
    ∃ K : C((X × _root_.stdSimplex ℝ (Fin (n + 1))) × I, Y),
      (∀ x b, K ((x, b), 0) = f (x, b)) ∧
      ∀ x (b : boundary n) t, K ((x, b.1), t) = H ((x, b), t) := by
  exact exists_homotopy_extension_of_cylinder_retraction (boundary n)
    (isClosed_boundary n) (simplexBoundaryCylinderRetraction n)
    (simplexBoundaryCylinderRetraction_coe n) f H h

end stdSimplex
