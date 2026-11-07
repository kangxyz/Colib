/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, kangxyz
-/
module

public import Colib.GroupTheory.MonoidHom.CentralLifts
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# CentralKernel

Adapted from `Quillen/Aglib/Algebra/Group/Hom/CentralKernel.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual maps and hypotheses.

The declarations retain their original field, rank, central-kernel and explicit
transport hypotheses. Their current consumer is the finite Matsumoto normalizer,
Bruhat action, or conditional original-root detector construction.

-/

@[expose] public section

/-! ## CentralDoubling -/

section

open scoped commutatorElement

universe u v

namespace MonoidHom.CentralKernel.Doubling

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- A central element cannot be squared by inner conjugation unless it is one. -/
theorem eq_one_of_central_of_conj_square {z d : G}
    (hz : z ∈ Subgroup.center G) (hd : d * z * d⁻¹ = z ^ 2) : z = 1 := by
  have hfix : d * z * d⁻¹ = z := by
    rw [Subgroup.mem_center_iff.mp hz d, mul_inv_cancel_right]
  have he : z * 1 = z * z := by simpa only [mul_one, pow_two] using hfix.symm.trans hd
  exact (mul_left_cancel he).symm

/-- Equal projections and simultaneous squaring force equal lifts across a central kernel. -/
theorem eq_of_central_ker_of_conj_square (p : G →* H)
    (hc : p.ker ≤ Subgroup.center G) {a b d : G} (hab : p a = p b)
    (ha : d * a * d⁻¹ = a ^ 2) (hb : d * b * d⁻¹ = b ^ 2) : a = b := by
  let z := a * b⁻¹
  have hz : z ∈ Subgroup.center G := hc (by simp [z, MonoidHom.mem_ker, hab])
  have haz : a = z * b := by simp [z, mul_assoc]
  have habc : Commute a b := by
    rw [haz]
    have hzb : Commute z b := (Subgroup.mem_center_iff.mp hz b).symm
    exact hzb.mul_left (Commute.refl b)
  have hd : d * z * d⁻¹ = z ^ 2 := by
    calc
      d * z * d⁻¹ = (d * a * d⁻¹) * (d * b * d⁻¹)⁻¹ := by simp [z, mul_assoc]
      _ = a ^ 2 * (b ^ 2)⁻¹ := by rw [ha, hb]
      _ = z ^ 2 := by simp only [z, habc.inv_right.mul_pow, inv_pow]
  have hone := eq_one_of_central_of_conj_square hz hd
  exact mul_inv_eq_one.mp hone

/-- A central commutator vanishes if one factor is doubled and the other fixed. -/
theorem commute_of_central_ker_of_conj_square (p : G →* H)
    (hc : p.ker ≤ Subgroup.center G) {a b d : G} (hab : Commute (p a) (p b))
    (ha : d * a * d⁻¹ = a ^ 2) (hb : d * b * d⁻¹ = b) : Commute a b := by
  have hz : ⁅a, b⁆ ∈ Subgroup.center G := hc (by
    simp only [MonoidHom.mem_ker, map_commutatorElement]
    exact hab.commutator_eq)
  have hcomm : Commute a ⁅a, b⁆ := Subgroup.mem_center_iff.mp hz a
  apply commutatorElement_eq_one_iff_commute.mp
  apply eq_one_of_central_of_conj_square hz
  rw [conjugate_commutatorElement, ha, hb]
  exact (hcomm.commutatorElement_pow_left 2).symm

/-- The output root need only commute with the first factor of the chain. -/
theorem chain_of_central_ker_of_conj_square (p : G →* H)
    (hc : p.ker ≤ Subgroup.center G) {a b c d : G}
    (hproj : p ⁅a, b⁆ = p c) (hac : Commute a c)
    (ha : d * a * d⁻¹ = a ^ 2) (hb : d * b * d⁻¹ = b)
    (hc' : d * c * d⁻¹ = c ^ 2) : ⁅a, b⁆ = c := by
  have hz : ⁅a, b⁆ * c⁻¹ ∈ Subgroup.center G := hc (by
    simp [MonoidHom.mem_ker, hproj])
  have he : ⁅a, b⁆ = (⁅a, b⁆ * c⁻¹) * c := by simp
  have hcomm : Commute a ⁅a, b⁆ := by
    rw [he]
    have haz : Commute a (⁅a, b⁆ * c⁻¹) := Subgroup.mem_center_iff.mp hz a
    exact haz.mul_right hac
  apply eq_of_central_ker_of_conj_square p hc hproj _ hc'
  rw [conjugate_commutatorElement, ha, hb]
  exact (hcomm.commutatorElement_pow_left 2).symm

end MonoidHom.CentralKernel.Doubling

end

/-! ## CentralCommutator -/

section

/-!
# Commutators are independent of lifts across a central kernel

The projection need not be surjective. Equality of the two projected pairs is
enough to identify their commutators, because each change of lift is central.
-/
namespace MonoidHom.CentralKernel

open scoped commutatorElement

variable {E G H : Type*} [Group E] [Group G] [Group H]

/-- Commutators depend only on the two projected elements when the kernel is central. -/
theorem commutator_eq_of_projection_eq (p : E →* G) (hcentral : p.ker ≤ Subgroup.center E)
    {x x' y y' : E} (hx : p x = p x') (hy : p y = p y') : ⁅x, y⁆ = ⁅x', y'⁆ := by
  have hz : x'⁻¹ * x ∈ Subgroup.center E := hcentral (by
    change p (x'⁻¹ * x) = 1
    rw [map_mul, map_inv, hx, inv_mul_cancel])
  have hw : y'⁻¹ * y ∈ Subgroup.center E := hcentral (by
    change p (y'⁻¹ * y) = 1
    rw [map_mul, map_inv, hy, inv_mul_cancel])
  have hzy : Commute (x'⁻¹ * x) y :=
    (show Commute y (x'⁻¹ * x) from (Subgroup.mem_center_iff.mp hz) y).symm
  have hxw : Commute x' (y'⁻¹ * y) := (Subgroup.mem_center_iff.mp hw) x'
  calc
    ⁅x, y⁆ = ⁅x' * (x'⁻¹ * x), y⁆ := by simp
    _ = ⁅x', y⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul, hzy.commutator_eq]
      simp
    _ = ⁅x', y' * (y'⁻¹ * y)⁆ := by simp
    _ = ⁅x', y'⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj, hxw.commutator_eq]
      simp

/-- Actual torus lifts can replace projected root words when computing their commutator. -/
theorem commutator_eq_torus_commutator (p : E →* G)
    (hcentral : p.ker ≤ Subgroup.center E) (τ : H →* E)
    {x y : E} {a b : H} (hx : p x = p (τ a)) (hy : p y = p (τ b)) :
    ⁅x, y⁆ = τ ⁅a, b⁆ := by
  rw [commutator_eq_of_projection_eq p hcentral hx hy]
  exact (map_commutatorElement τ a b).symm

end MonoidHom.CentralKernel

end
