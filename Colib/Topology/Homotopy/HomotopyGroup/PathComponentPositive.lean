/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.Map

/-! # Original component inclusion on every positive homotopy group -/
/-! Implementation source: `Quillen/Topology/HomotopyGroups/PathComponentPositive.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual maps, endpoint paths,
universes and signs are retained, with native Colib dependencies. -/
@[expose] public section
noncomputable section
open scoped Topology unitInterval
universe u v
namespace Topology
variable {X : Type u} [TopologicalSpace X] (x : X)

/-- The literal inclusion of the path component of the supplied point. -/
def pathComponentInclusion : C(pathComponent x, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private def intervalZeroPath (t : unitInterval) : Path 0 t where
  toFun s := s * t
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.mul_const (t : ℝ)
  source' := zero_mul t
  target' := one_mul t

private lemma cubeZeroJoined {N : Type v} (t : N → unitInterval) : Joined 0 t :=
  Joined.pi fun i ↦ ⟨intervalZeroPath (t i)⟩

variable {N : Type v} [Nonempty N]

/-- A based cube of positive dimension lies wholly in its basepoint component. -/
lemma genLoop_mem_pathComponent (p : GenLoop N X x) (t : N → unitInterval) :
    p t ∈ pathComponent x := by
  have h := (cubeZeroJoined t).map p.val.continuous
  rw [p.property 0 ⟨Classical.arbitrary N, Or.inl rfl⟩] at h
  exact h

/-- Restrict the original based cube, without changing any point. -/
def genLoopToPathComponent (p : GenLoop N X x) :
    GenLoop N (pathComponent x) ⟨x, mem_pathComponent_self x⟩ :=
  ⟨⟨fun t ↦ ⟨p t, genLoop_mem_pathComponent x p t⟩, p.val.continuous.subtype_mk _⟩,
    fun t ht ↦ Subtype.ext (p.property t ht)⟩

/-- Every point of a boundary-fixed positive cube homotopy lies in the base component. -/
lemma genLoopHomotopy_mem_pathComponent
    {p q : GenLoop N (pathComponent x) ⟨x, mem_pathComponent_self x⟩}
    (H : (GenLoop.postcomp (pathComponentInclusion x) rfl p).val.HomotopyRel
      (GenLoop.postcomp (pathComponentInclusion x) rfl q).val (Cube.boundary N))
    (z : unitInterval × (N → unitInterval)) : H z ∈ pathComponent x := by
  have h := ((show Joined (0 : unitInterval) z.1 from ⟨intervalZeroPath z.1⟩).prod
    (cubeZeroJoined z.2)).map H.continuous
  have hz : H (0, 0) = x := by
    rw [H.apply_zero]
    exact congrArg Subtype.val (p.property 0 ⟨Classical.arbitrary N, Or.inl rfl⟩)
  rw [hz] at h
  exact h

/-- Restrict an actual boundary-fixed homotopy to the original component. -/
def genLoopPathComponentHomotopy
    {p q : GenLoop N (pathComponent x) ⟨x, mem_pathComponent_self x⟩}
    (H : (GenLoop.postcomp (pathComponentInclusion x) rfl p).val.HomotopyRel
      (GenLoop.postcomp (pathComponentInclusion x) rfl q).val (Cube.boundary N)) :
    p.val.HomotopyRel q.val (Cube.boundary N) where
  toFun z := ⟨H z, genLoopHomotopy_mem_pathComponent x H z⟩
  continuous_toFun := H.continuous.subtype_mk _
  map_zero_left t := Subtype.ext (H.apply_zero t)
  map_one_left t := Subtype.ext (H.apply_one t)
  prop' t _s hs := Subtype.ext (H.eq_fst t hs)

/-- The original inclusion induces a bijection on positive-dimensional homotopy classes. -/
theorem homotopyGroupMap_pathComponent_bijective :
    Function.Bijective (HomotopyGroup.map (N := N) (pathComponentInclusion x)
      (x := ⟨x, mem_pathComponent_self x⟩) rfl) := by
  constructor
  · intro a b h
    induction a using Quotient.inductionOn with | h p =>
    induction b using Quotient.inductionOn with | h q =>
      obtain ⟨H⟩ := Quotient.exact h
      exact Quotient.sound ⟨genLoopPathComponentHomotopy x H⟩
  · intro a
    induction a using Quotient.inductionOn with | h p =>
      refine ⟨Quotient.mk' (genLoopToPathComponent x p), ?_⟩
      rfl

/-- Positive homotopy groups of a component retain the original inclusion homomorphism. -/
def pathComponentPiMulEquiv (n : ℕ) :
    HomotopyGroup.Pi (n + 1) (pathComponent x) ⟨x, mem_pathComponent_self x⟩ ≃*
      HomotopyGroup.Pi (n + 1) X x :=
  MulEquiv.ofBijective (HomotopyGroup.mapHom (N := Fin (n + 1))
    (pathComponentInclusion x) (x := ⟨x, mem_pathComponent_self x⟩) rfl)
      (homotopyGroupMap_pathComponent_bijective x)

end Topology
