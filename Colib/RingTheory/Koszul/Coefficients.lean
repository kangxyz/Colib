/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Motivic Cohomology contributors
-/
module

public import Colib.Util.References
public import StacksFrontier.RingTheory.Koszul.Defs
public import StacksFrontier.RingTheory.Tor.AlmostFlatResolution
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Finiteness and coefficient annihilators for Koszul complexes

These statements use Stacks' exterior-power Koszul complex with coefficients.
Finite coefficients give finite terms, and Noetherianity of the ring makes the
homology Noetherian. The coefficient annihilator annihilates each term and its
homology without finiteness or regularity assumptions.

Adapted from `Aglib.Algebra.Homology.Koszul.Coefficient.Finite` at revision
`101dbb8564fb0e29f28cfcb79168d878b5ab489f`, originally migrated from Motivic's
`KoszulCoefficientFiniteness.lean`. The source's recursive tensor model is not
reconstructed. The tensor-product and homology annihilator facts are reused
from Stacks, and finiteness uses Mathlib's existing exterior-power and tensor
product instances.
-/

@[expose] public section

open CategoryTheory
open scoped ExteriorAlgebra TensorProduct

universe u

namespace Koszul

variable {R : Type u} [CommRing R] {r : ℕ}

/-- Finite coefficients give finite terms in the native Koszul complex. -/
instance seqComplexTensor_finite_X (f : Fin r → R) (M : ModuleCat.{u} R)
    [Module.Finite R M] (n : ℕ) : Module.Finite R ((seqComplexTensor f M).X n) :=
  inferInstanceAs (Module.Finite R ((⋀[R]^n (Fin r → R)) ⊗[R] M))

/-- Over a Noetherian ring, finite coefficients give Noetherian Koszul homology. -/
instance seqComplexTensor_noetherian_homology [IsNoetherianRing R]
    (f : Fin r → R) (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    IsNoetherian R ((seqComplexTensor f M).homology n) := by
  have : IsNoetherian R ((seqComplexTensor f M).cycles n) :=
    isNoetherian_of_injective ((seqComplexTensor f M).iCycles n).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  exact isNoetherian_of_surjective ((seqComplexTensor f M).homologyπ n).hom
    (LinearMap.range_eq_top.mpr ((ModuleCat.epi_iff_surjective _).mp inferInstance))

/-- The coefficient annihilator annihilates each term, without regularity or
finiteness assumptions. -/
theorem annihilator_le_annihilator_seqComplexTensor_X
    (f : Fin r → R) (M : ModuleCat.{u} R) (n : ℕ) :
    Module.annihilator R M ≤ Module.annihilator R ((seqComplexTensor f M).X n) := by
  intro a ha
  change a ∈ Module.annihilator R ((⋀[R]^n (Fin r → R)) ⊗[R] M)
  have h : a ∈ Module.annihilator R (M ⊗[R] (⋀[R]^n (Fin r → R))) :=
    mem_annihilator_tensor_of_mem_annihilator ha (ModuleCat.of R (⋀[R]^n (Fin r → R)))
  rwa [(TensorProduct.comm R M (⋀[R]^n (Fin r → R))).annihilator_eq] at h

/-- The coefficient annihilator annihilates native Koszul homology, without
regularity or finiteness assumptions. -/
theorem annihilator_le_annihilator_seqComplexTensor_homology
    (f : Fin r → R) (M : ModuleCat.{u} R) (n : ℕ) :
    Module.annihilator R M ≤ Module.annihilator R ((seqComplexTensor f M).homology n) := by
  intro a ha
  have hterm : a ∈ Module.annihilator R ((seqComplexTensor f M).X n) :=
    annihilator_le_annihilator_seqComplexTensor_X f M n ha
  exact mem_annihilator_homology_of_mem_annihilator
    (A := R) (c := ComplexShape.down ℕ) (seqComplexTensor f M) n hterm

end Koszul

attribute [colib_tag "COL-0031"] Koszul.seqComplexTensor_finite_X
  Koszul.seqComplexTensor_noetherian_homology
  Koszul.annihilator_le_annihilator_seqComplexTensor_X
  Koszul.annihilator_le_annihilator_seqComplexTensor_homology

add_to_stacks 0623
  "Definition ingredient: finite-sequence exterior Koszul complex, tensored with coefficients"
  Koszul.seqComplexTensor_finite_X
add_to_stacks 00IK
  "Ingredient: submodules of finite modules over a Noetherian ring are finite"
  Koszul.seqComplexTensor_noetherian_homology
add_to_stacks 0622
  "Definition ingredient only: exterior Koszul terms, here tensored with a coefficient module"
  Koszul.annihilator_le_annihilator_seqComplexTensor_X
add_to_stacks 0623
  "Definition ingredient only; coefficient-annihilator inclusion is proved here, not in this tag"
  Koszul.annihilator_le_annihilator_seqComplexTensor_homology
