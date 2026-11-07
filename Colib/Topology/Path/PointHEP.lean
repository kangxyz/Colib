/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.PointCylinder
public import Mathlib.Topology.Path
public import Mathlib.Topology.Order.Compact

/-!
# Homotopy extension at the constant loop

A closed point with HEP gives HEP at the constant loop in the actual compact-open
path space. Apply its literal point-cylinder retraction pointwise to a loop and
take the minimum output height over the compact interval. Positive minimum
forces the entire output loop to be constant. This produces the original
loop-space cylinder retraction, without changing its topology or requiring CW
or local compactness hypotheses on the ambient space.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/Path/PointHEP.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original objects, maps,
point hypotheses, whole stored cylinder paths and universe parameters are
retained. Native namespace and lower-import ownership are used. -/
@[expose] public section

noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology
variable {X : Type u} [TopologicalSpace X] {x : X}
namespace PointCylinderRetraction

/-- The minimum original retraction height over the entire compact loop parameter. -/
def loopHeight (R : PointCylinderRetraction x) : C(unitInterval × Path x x, unitInterval) where
  toFun z := sInf ((fun s : unitInterval ↦ (R.map (z.1, z.2 s)).1.1) '' Set.univ)
  continuous_toFun := isCompact_univ.continuous_sInf (by fun_prop)

/-- Apply the original retraction's space coordinate to the entire based loop. -/
def loopPath (R : PointCylinderRetraction x) : C(unitInterval × Path x x, Path x x) where
  toFun z := {
    toFun s := (R.map (z.1, z.2 s)).1.2
    continuous_toFun := by fun_prop
    source' := by rw [z.2.source, R.at_point]
    target' := by rw [z.2.target, R.at_point] }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : (unitInterval × Path x x) × unitInterval ↦
      (R.map (z.1.1, z.1.2 z.2)).1.2)
    fun_prop

/-- Positive minimum height forces the whole original output loop to be constant. -/
theorem loopPath_eq_refl_of_loopHeight_ne_zero (R : PointCylinderRetraction x)
    (z : unitInterval × Path x x) (hz : R.loopHeight z ≠ 0) : R.loopPath z = Path.refl x := by
  apply Path.ext
  funext s
  change (R.map (z.1, z.2 s)).1.2 = x
  apply (R.map (z.1, z.2 s)).2.resolve_left
  intro ht
  apply hz
  apply le_antisymm
  · exact ht ▸ (sInf_le (Set.mem_image_of_mem _ (Set.mem_univ s)))
  · exact unitInterval.nonneg'

/-- The compact minimum makes the pointwise construction a literal loop-cylinder retraction. -/
def loop (R : PointCylinderRetraction x) : PointCylinderRetraction (Path.refl x) where
  map := {
    toFun z := ⟨(R.loopHeight z, R.loopPath z), by
      by_cases hz : R.loopHeight z = 0
      · exact Or.inl hz
      · exact Or.inr (R.loopPath_eq_refl_of_loopHeight_ne_zero z hz)⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact R.loopHeight.continuous.prodMk R.loopPath.continuous }
  at_zero γ := by
    apply Subtype.ext
    apply Prod.ext
    · change R.loopHeight (0, γ) = 0
      simp [loopHeight, R.at_zero]
    · apply Path.ext
      funext s
      change (R.map (0, γ s)).1.2 = γ s
      rw [R.at_zero]
  at_point t := by
    apply Subtype.ext
    apply Prod.ext
    · change R.loopHeight (t, Path.refl x) = t
      simp [loopHeight, R.at_point]
    · apply Path.ext
      funext s
      change (R.map (t, x)).1.2 = x
      rw [R.at_point]

end PointCylinderRetraction
end Topology

namespace Path
open Topology
variable {X : Type u} [TopologicalSpace X] {x : X}

/-- Closedness of the original point gives closedness of the actual constant loop singleton. -/
theorem isClosed_singleton_refl (hx : IsClosed ({x} : Set X)) :
    IsClosed ({Path.refl x} : Set (Path x x)) := by
  have he : ({Path.refl x} : Set (Path x x)) =
      ⋂ t : unitInterval, {γ : Path x x | γ t = x} := by
    ext γ
    simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · rintro rfl t
      rfl
    · intro h
      apply Path.ext
      funext t
      exact h t
  rw [he]
  exact isClosed_iInter (fun t ↦ hx.preimage (by fun_prop))

/-- A closed actual point with HEP remains well-based after actual compact-open looping. -/
theorem homotopyExtensionProperty_refl
    (hx : IsClosed ({x} : Set X))
    (hHEP : TopCat.HomotopyExtensionProperty (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} x))) :
    TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (Path.refl x))) := by
  obtain ⟨R⟩ := PointCylinderRetraction.nonempty_of_homotopyExtensionProperty x hHEP
  exact R.loop.homotopyExtensionProperty (isClosed_singleton_refl hx)

end Path
