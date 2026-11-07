/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.ExtensionContinuous
public import Mathlib.Topology.Piecewise

/-!
# The literal point-cylinder retraction criterion for HEP

Point HEP supplies a retraction of the original cylinder to its bottom together
with the basepoint line. Conversely, when the point is closed, this literal
subspace retraction gives HEP by closed-set pasting. No replacement of the
underlying space or cylinder topology is involved.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/HELP/PointCylinder.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original objects, maps,
point hypotheses, whole stored cylinder paths and universe parameters are
retained. Native namespace and lower-import ownership are used. -/
@[expose] public section

noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology
variable {X : Type u} [TopologicalSpace X]

/-- The bottom of the actual cylinder together with its original basepoint line. -/
def PointCylinder (x : X) := {z : unitInterval × X // z.1 = 0 ∨ z.2 = x}

instance (x : X) : TopologicalSpace (PointCylinder x) :=
  inferInstanceAs (TopologicalSpace {z : unitInterval × X // z.1 = 0 ∨ z.2 = x})

/-- An actual continuous point-cylinder retraction, with both fixed faces displayed. -/
structure PointCylinderRetraction (x : X) where
  /-- The continuous retraction into the literal cylinder subspace. -/
  map : C(unitInterval × X, PointCylinder x)
  at_zero (y : X) : map (0, y) = ⟨(0, y), Or.inl rfl⟩
  at_point (t : unitInterval) : map (t, x) = ⟨(t, x), Or.inr rfl⟩

namespace PointCylinderRetraction

/-- Actual point HEP extends the two tautological faces into the original cylinder subspace. -/
theorem nonempty_of_homotopyExtensionProperty (x : X)
    (hx : TopCat.HomotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} x))) :
    Nonempty (PointCylinderRetraction x) := by
  let f : C(X, PointCylinder x) := ⟨fun y ↦ ⟨(0, y), Or.inl rfl⟩, by fun_prop⟩
  let H : C(unitInterval × PUnit.{u + 1}, PointCylinder x) :=
    ⟨fun z ↦ ⟨(z.1, x), Or.inr rfl⟩, by fun_prop⟩
  obtain ⟨K, hK₀, hK⟩ := TopCat.homotopyExtensionProperty_continuous hx
    (TopCat.of (PointCylinder x)) f H (by intro a; rfl)
  exact ⟨⟨K, hK₀, fun t ↦ hK t PUnit.unit⟩⟩

/-- A literal point-cylinder retraction gives HEP when its original basepoint is closed. -/
theorem homotopyExtensionProperty {x : X} (R : PointCylinderRetraction x)
    (hx : IsClosed ({x} : Set X)) :
    TopCat.HomotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} x)) := by
  classical
  apply TopCat.homotopyExtensionProperty_of_continuous
  intro Z f H h₀
  let p : PointCylinder x → Z := fun z ↦ if z.1.1 = 0 then f z.1.2 else H (z.1.1, PUnit.unit)
  have hp : Continuous p := by
    apply Continuous.if
    · intro z hz
      have hbottom : IsClosed {z : PointCylinder x | z.1.1 = 0} :=
        isClosed_eq (by fun_prop) continuous_const
      have hpoint : IsClosed {z : PointCylinder x | z.1.2 = x} :=
        hx.preimage (by fun_prop)
      have htime : z.1.1 = 0 := hbottom.frontier_subset hz
      have hbase : z.1.2 = x := by
        rw [frontier_eq_closure_inter_closure] at hz
        exact closure_minimal (fun w hw ↦ w.2.resolve_left hw) hpoint hz.2
      rw [htime, hbase]
      exact (h₀ PUnit.unit).symm
    · fun_prop
    · fun_prop
  refine ⟨(⟨p, hp⟩ : C(PointCylinder x, Z)).comp R.map, ?_, ?_⟩
  · intro y
    change p (R.map (0, y)) = f y
    rw [R.at_zero]
    simp only [p, ite_eq_left rfl]
  · intro t a
    change p (R.map (t, x)) = H (t, a)
    rw [R.at_point]
    dsimp only [p]
    split_ifs with ht
    · subst t
      exact (h₀ a).symm
    · congr 1

end PointCylinderRetraction
end Topology
