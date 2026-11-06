/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.UnitInterval
public import Colib.Topology.HELP.CylinderBoundary
public import Mathlib.Topology.Homotopy.HomotopyGroup

/-! # Genuine compact HEP presentations of finite cube boundaries

The boundary is built from the empty boundary of the zero-cube by the actual
pushout cylinder construction. Its image is exactly the original `Cube.boundary`.
No injectivity or boundary homeomorphism is needed for the later lifting tests.


Implementation provenance:
`Quillen/Topology/HELP/CubeBoundary.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits
open scoped Topology unitInterval
universe u
namespace Topology.CubicalTests

/-- Universe-lifted actual finite cubes, with their original product topology. -/
abbrev cube (n : ℕ) : TopCat.{u} := TopCat.of (ULift.{u} (Fin n → unitInterval))

instance cube_compactSpace (n : ℕ) : CompactSpace (cube.{u} n) := by
  change CompactSpace (ULift.{u} (Fin n → unitInterval))
  infer_instance

/-- The vertex of the universe-lifted finite cube with every coordinate equal to zero. -/
def zero (n : ℕ) : cube.{u} n := ⟨fun _ ↦ 0⟩

/-- The original linear coordinate contraction, requiring no chosen path family. -/
def contraction (n : ℕ) : (ContinuousMap.id (cube.{u} n)).Homotopy
    (ContinuousMap.const _ (zero n)) where
  toFun z := ⟨fun j ↦ unitInterval.symm z.1 * z.2.down j⟩
  continuous_toFun := by
    apply continuous_uliftUp.comp
    apply continuous_pi
    intro j
    fun_prop
  map_zero_left x := by apply ULift.ext; funext j; simp
  map_one_left x := by apply ULift.ext; funext j; simp [zero]

/-- Adjoin the first coordinate to the actual cube. -/
def stepHomeomorph (n : ℕ) : (cube.{u} n × unitInterval) ≃ₜ cube.{u} (n+1) where
  toFun z := ⟨Fin.cons z.2 z.1.down⟩
  invFun z := (⟨Fin.tail z.down⟩, z.down 0)
  left_inv _ := rfl
  right_inv z := by
    apply ULift.ext
    funext i
    cases i using Fin.cases <;> rfl
  continuous_toFun := by
    apply continuous_uliftUp.comp
    apply continuous_pi
    intro i
    cases i using Fin.cases
    · exact continuous_snd
    · fun_prop
  continuous_invFun := by fun_prop

/-- A compact HEP map presenting precisely the entire ordinary cube boundary. -/
structure BoundaryPresentation (n : ℕ) where
  /-- The compact parameter space presenting the finite cube boundary. -/
  space : TopCat.{u}
  /-- The boundary presentation space is compact. -/
  compact : CompactSpace space
  /-- The presentation map into the universe-lifted `n`-cube. -/
  map : space ⟶ cube.{u} n
  /-- The presentation map has the homotopy extension property. -/
  hep : TopCat.HomotopyExtensionProperty map
  /-- Every image point lies in the original finite cube boundary. -/
  lands : ∀ a, (map a).down ∈ Cube.boundary (Fin n)
  /-- Every point of the original finite cube boundary has a presentation preimage. -/
  covers : ∀ z : cube.{u} n, z.down ∈ Cube.boundary (Fin n) → ∃ a, map a = z

/-- The zero-dimensional boundary is genuinely empty. -/
def emptyBoundary : BoundaryPresentation.{u} 0 where
  space := TopCat.of PEmpty.{u+1}
  compact := inferInstance
  map := TopCat.ofHom ⟨isEmptyElim, continuous_of_discreteTopology⟩
  hep := by
    apply TopCat.homotopyExtensionProperty_of_continuous
    intro Z f H _
    exact ⟨f.comp ContinuousMap.snd, fun _ ↦ rfl, fun _ a ↦ isEmptyElim a⟩
  lands := fun a ↦ isEmptyElim a
  covers := by rintro z ⟨i, _⟩; exact Fin.elim0 i

/-- Iterate the actual compact cylinder-boundary pushout, including both caps. -/
def BoundaryPresentation.step {n : ℕ} (P : BoundaryPresentation.{u} n) :
    BoundaryPresentation.{u} (n+1) := by
  let : CompactSpace P.space := P.compact
  let j := TopCat.CylinderBoundary.cylinderBoundaryMap P.map ≫ (TopCat.isoOfHomeo (stepHomeomorph
    n)).hom
  have hs (a : P.space) (t : unitInterval) :
      j (TopCat.CylinderBoundary.cylinderBoundarySide P.map (a,t)) = ⟨Fin.cons t (P.map a).down⟩ :=
    congrArg (stepHomeomorph n) (ConcreteCategory.congr_hom
      (TopCat.CylinderBoundary.cylinderBoundarySide_map P.map) (a,t))
  have h₀ (x : cube.{u} n) :
      j (TopCat.CylinderBoundary.cylinderBoundaryCaps P.map (Sum.inl x)) = ⟨Fin.cons 0 x.down⟩ :=
    congrArg (stepHomeomorph n) (ConcreteCategory.congr_hom
      (TopCat.CylinderBoundary.cylinderBoundaryCaps_map P.map)
      (Sum.inl x))
  have h₁ (x : cube.{u} n) :
      j (TopCat.CylinderBoundary.cylinderBoundaryCaps P.map (Sum.inr x)) = ⟨Fin.cons 1 x.down⟩ :=
    congrArg (stepHomeomorph n) (ConcreteCategory.congr_hom
      (TopCat.CylinderBoundary.cylinderBoundaryCaps_map P.map)
      (Sum.inr x))
  refine {
    space := TopCat.CylinderBoundary P.map
    compact := inferInstance
    map := j
    hep := TopCat.homotopyExtensionProperty_comp
      (TopCat.CylinderBoundary.homotopyExtensionProperty_cylinderBoundaryMap P.map P.hep)
      (TopCat.homotopyExtensionProperty_of_isIso _)
    lands := ?_
    covers := ?_ }
  · intro z
    obtain ⟨z, rfl⟩ := pushout_sum_surjective (TopCat.CylinderBoundary.cylinderBoundary_isPushout
      P.map) z
    rcases z with ⟨a,t⟩ | (x | x)
    · change (j (TopCat.CylinderBoundary.cylinderBoundarySide P.map (a,t))).down ∈ Cube.boundary
        (Fin (n+1))
      rw [hs]
      obtain ⟨k, hk⟩ := P.lands a
      exact ⟨k.succ, hk⟩
    · change (j (TopCat.CylinderBoundary.cylinderBoundaryCaps P.map (Sum.inl x))).down ∈
        Cube.boundary (Fin (n+1))
      rw [h₀]
      exact ⟨0, Or.inl rfl⟩
    · change (j (TopCat.CylinderBoundary.cylinderBoundaryCaps P.map (Sum.inr x))).down ∈
        Cube.boundary (Fin (n+1))
      rw [h₁]
      exact ⟨0, Or.inr rfl⟩
  · rintro z ⟨k, hk⟩
    cases k using Fin.cases with
    | zero =>
      rcases hk with hk | hk
      · refine ⟨TopCat.CylinderBoundary.cylinderBoundaryCaps P.map (Sum.inl ⟨Fin.tail z.down⟩), ?_⟩
        rw [h₀]
        apply ULift.ext
        funext k
        cases k using Fin.cases
        · exact hk.symm
        · rfl
      · refine ⟨TopCat.CylinderBoundary.cylinderBoundaryCaps P.map (Sum.inr ⟨Fin.tail z.down⟩), ?_⟩
        rw [h₁]
        apply ULift.ext
        funext k
        cases k using Fin.cases
        · exact hk.symm
        · rfl
    | succ k =>
      obtain ⟨a, ha⟩ := P.covers ⟨Fin.tail z.down⟩ ⟨k, hk⟩
      refine ⟨TopCat.CylinderBoundary.cylinderBoundarySide P.map (a,z.down 0), ?_⟩
      rw [hs, ha]
      apply ULift.ext
      funext k
      cases k using Fin.cases <;> rfl

/-- The canonical iterated pushout presentation in every finite dimension. -/
def boundaryPresentation : (n : ℕ) → BoundaryPresentation.{u} n
  | 0 => emptyBoundary
  | n+1 => (boundaryPresentation n).step

theorem boundaryPresentation_range (n : ℕ) :
    Set.range (boundaryPresentation.{u} n).map =
      {z : cube.{u} n | z.down ∈ Cube.boundary (Fin n)} := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    exact (boundaryPresentation n).lands a
  · exact (boundaryPresentation n).covers z

end Topology.CubicalTests
