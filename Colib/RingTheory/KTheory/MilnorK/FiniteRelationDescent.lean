/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.RingTheory.KTheory.MilnorK.FiniteTensorEquality
public import Colib.RingTheory.KTheory.MilnorK.FiniteClassDescent

/-!
# Finite-stage vanishing and equality of native Milnor classes

Vanishing after an algebraic extension already holds over one actual finite
intermediate field. The argument combines finite Steinberg-ideal preimages
with eventual equality of prescribed native tensors. It does not assert
injectivity of tensor transport, introduce another presentation, or use norms.

The last two endpoints adapt `Aglib.KTheory.MilnorK.FiniteRelationDescent`,
lines 175-204, at revision `101dbb8564fb0e29f28cfcb79168d878b5ab489f` to the
chosen native homogeneous groups. Degree zero, inseparability, the original
coefficient maps, and independent field universes are retained. The stronger
finite-enlargement statements also retain a prescribed finite starting field.
-/

@[expose] public noncomputable section

universe u v

variable (k : Type u) (E : Type v) [Field k] [Field E]
variable [Algebra k E] [Algebra.IsAlgebraic k E]

/-- A prescribed tensor whose image lies in the native Steinberg ideal lies
in that ideal after one finite enlargement of its finite field of definition. -/
theorem exists_finite_milnorKTensor_mem_steinberg (S : IntermediateField k E)
    [FiniteDimensional k S] (x : MilnorKTensorAlgebra S)
    (hx : milnorKTensorMap S.val.toRingHom x ∈ milnorKSteinbergIdeal E) :
    ∃ T : IntermediateField k E, FiniteDimensional k T ∧
      ∃ hST : S ≤ T,
        milnorKTensorMap (IntermediateField.inclusion hST).toRingHom x ∈
          milnorKSteinbergIdeal T := by
  obtain ⟨U, hU, y, hy, hyx⟩ := exists_finite_milnorKSteinbergIdeal k E _ hx
  let := hU
  let iS := (IntermediateField.inclusion (show S ≤ S ⊔ U from le_sup_left)).toRingHom
  let iU := (IntermediateField.inclusion (show U ≤ S ⊔ U from le_sup_right)).toRingHom
  let a := milnorKTensorMap iS x
  let b := milnorKTensorMap iU y
  have hab : milnorKTensorMap (S ⊔ U).val.toRingHom a =
      milnorKTensorMap (S ⊔ U).val.toRingHom b := by
    exact (milnorKTensorMap_val_inclusion
      (show S ≤ S ⊔ U from le_sup_left) x).trans
        (hyx.symm.trans (milnorKTensorMap_val_inclusion
          (show U ≤ S ⊔ U from le_sup_right) y).symm)
  obtain ⟨T, hT, hVT, hTxy⟩ := exists_finite_milnorKTensor_eq k E (S ⊔ U) a b hab
  let hST : S ≤ T := le_sup_left.trans hVT
  refine ⟨T, hT, hST, ?_⟩
  have hfirst : milnorKTensorMap (IntermediateField.inclusion hST).toRingHom x =
      milnorKTensorMap (IntermediateField.inclusion hVT).toRingHom a := by
    symm
    exact milnorKTensorMap_inclusion_inclusion le_sup_left hVT x
  rw [hfirst, hTxy]
  exact milnorKTensorMap_mem_milnorKSteinbergIdeal _
    (milnorKTensorMap_mem_milnorKSteinbergIdeal iU hy)

/-- Vanishing of an actual Milnor-ring element after extension is witnessed
in a finite enlargement of its finite intermediate field. -/
theorem exists_finite_milnorKRing_eq_zero (S : IntermediateField k E)
    [FiniteDimensional k S] (x : MilnorKRing S)
    (hx : milnorKRingMap S.val.toRingHom x = 0) :
    ∃ T : IntermediateField k E, FiniteDimensional k T ∧
      ∃ hST : S ≤ T,
        milnorKRingMap (IntermediateField.inclusion hST).toRingHom x = 0 := by
  obtain ⟨a, rfl⟩ := (milnorKSteinbergIdeal S).ringCon.mk'_surjective x
  have ha : milnorKTensorMap S.val.toRingHom a ∈ milnorKSteinbergIdeal E := by
    rw [← TwoSidedIdeal.ker_ringCon_mk' (milnorKSteinbergIdeal E), TwoSidedIdeal.mem_ker]
    exact hx
  obtain ⟨T, hT, hST, haT⟩ := exists_finite_milnorKTensor_mem_steinberg k E S a ha
  refine ⟨T, hT, hST, ?_⟩
  rw [milnorKRingMap_mk', ← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']
  exact haT

/-- Vanishing of a native homogeneous class from a finite intermediate field
is witnessed in a finite enlargement, with the starting field retained. -/
theorem exists_finite_milnorKTheory_eq_zero_over (S : IntermediateField k E)
    [FiniteDimensional k S] (n : ℕ) (x : MilnorKTheory S n)
    (hx : milnorKTheoryMap S.val.toRingHom n x = 0) :
    ∃ T : IntermediateField k E, FiniteDimensional k T ∧
      ∃ hST : S ≤ T,
        milnorKTheoryMap (IntermediateField.inclusion hST).toRingHom n x = 0 := by
  rw [milnorKTheoryMap_eq_transport] at hx
  have hxring := congrArg (fun z : MilnorKTheory E n => (z : MilnorKRing E)) hx
  change milnorKRingMap S.val.toRingHom (x : MilnorKRing S) = 0 at hxring
  obtain ⟨T, hT, hST, hzero⟩ := exists_finite_milnorKRing_eq_zero k E S x hxring
  refine ⟨T, hT, hST, ?_⟩
  rw [milnorKTheoryMap_eq_transport]
  exact Subtype.ext hzero

/-- Equality of native homogeneous classes is witnessed after a finite
enlargement of their finite intermediate field of definition. -/
theorem exists_finite_milnorKTheory_eq_over (S : IntermediateField k E)
    [FiniteDimensional k S] (n : ℕ) (x y : MilnorKTheory S n)
    (hxy : milnorKTheoryMap S.val.toRingHom n x =
      milnorKTheoryMap S.val.toRingHom n y) :
    ∃ T : IntermediateField k E, FiniteDimensional k T ∧
      ∃ hST : S ≤ T,
        milnorKTheoryMap (IntermediateField.inclusion hST).toRingHom n x =
          milnorKTheoryMap (IntermediateField.inclusion hST).toRingHom n y := by
  obtain ⟨T, hT, hST, hzero⟩ := exists_finite_milnorKTheory_eq_zero_over k E S n (x - y)
    (by rw [map_sub, hxy, sub_self])
  exact ⟨T, hT, hST, sub_eq_zero.mp (by simpa only [map_sub] using hzero)⟩

/-- Vanishing after an algebraic extension is witnessed over one actual finite
intermediate field, in every nonnegative degree and independent universes. -/
theorem exists_finite_intermediate_milnorKTheoryMap_eq_zero (n : ℕ)
    (x : MilnorKTheory k n) (hx : milnorKTheoryMap (algebraMap k E) n x = 0) :
    ∃ S : IntermediateField k E, FiniteDimensional k S ∧
      milnorKTheoryMap (algebraMap k S) n x = 0 := by
  let S₀ : IntermediateField k E := ⊥
  let x₀ := milnorKTheoryMap (algebraMap k S₀) n x
  have hcomp : RingHom.comp S₀.val.toRingHom (algebraMap k S₀) =
      (algebraMap k E : k →+* E) := by
    apply RingHom.ext
    intro a
    exact S₀.val.commutes a
  have hx₀ : milnorKTheoryMap S₀.val.toRingHom n x₀ = 0 := by
    change milnorKTheoryMap S₀.val.toRingHom n
      (milnorKTheoryMap (algebraMap k S₀) n x) = 0
    rw [← LinearMap.comp_apply, ← milnorKTheoryMap_comp, hcomp]
    exact hx
  obtain ⟨S, hS, h₀S, hzero⟩ := exists_finite_milnorKTheory_eq_zero_over k E S₀ n x₀ hx₀
  have hcompS : RingHom.comp (IntermediateField.inclusion h₀S).toRingHom
      (algebraMap k S₀) = (algebraMap k S : k →+* S) := by
    apply RingHom.ext
    intro a
    exact (IntermediateField.inclusion h₀S).commutes a
  refine ⟨S, hS, ?_⟩
  change milnorKTheoryMap (IntermediateField.inclusion h₀S).toRingHom n
    (milnorKTheoryMap (algebraMap k S₀) n x) = 0 at hzero
  rwa [← LinearMap.comp_apply, ← milnorKTheoryMap_comp, hcompS] at hzero

/-- Equality after an algebraic extension is witnessed over one actual finite
intermediate field. No characteristic or separability assumption is required. -/
theorem exists_finite_intermediate_milnorKTheoryMap_eq (n : ℕ)
    (x y : MilnorKTheory k n)
    (hxy : milnorKTheoryMap (algebraMap k E) n x =
      milnorKTheoryMap (algebraMap k E) n y) :
    ∃ S : IntermediateField k E, FiniteDimensional k S ∧
      milnorKTheoryMap (algebraMap k S) n x = milnorKTheoryMap (algebraMap k S) n y := by
  obtain ⟨S, hS, hzero⟩ := exists_finite_intermediate_milnorKTheoryMap_eq_zero k E n (x - y)
    (by rw [map_sub, hxy, sub_self])
  exact ⟨S, hS, sub_eq_zero.mp (by simpa only [map_sub] using hzero)⟩

add_to_stacks 0EAY
  "Derived finite-stage vanishing in the native quotient; not stated by the tag"
  exists_finite_intermediate_milnorKTheoryMap_eq_zero

attribute [colib_tag "COL-0264"]
  exists_finite_milnorKRing_eq_zero
  exists_finite_milnorKTheory_eq_zero_over
  exists_finite_milnorKTheory_eq_over
  exists_finite_intermediate_milnorKTheoryMap_eq_zero
  exists_finite_intermediate_milnorKTheoryMap_eq

attribute [colib_ref "aglib_principal_euler_pin"
  "KTheory/MilnorK/FiniteRelationDescent.lean:175-204" "adaptation"
  "Native finite-stage vanishing and equality in every degree and independent field universes"]
  exists_finite_intermediate_milnorKTheoryMap_eq_zero
  exists_finite_intermediate_milnorKTheoryMap_eq
