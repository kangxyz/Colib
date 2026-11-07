/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.HomotopyFiber.BasedLESNaturality
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalence

/-!
Implementation provenance:
`Quillen/Topology/HomotopyFiber/WeakBasePositive.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Base change on the original fiber fundamental group

A strictly commutative square with unchanged total space induces a bijection
on the actual fiber fundamental groups when its base map is bijective on
Pi two and injective on Pi one. The direct five-term argument retains the
original projection and connecting homomorphisms, in mixed universes.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w u' v'
open scoped Topology unitInterval
namespace Topology.HomotopyFiber

variable {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
  {f : C(X, Y)} {g : C(X', Y')}

section BaseChange
variable {A : Type v} {B : Type w} [TopologicalSpace A] [TopologicalSpace B]
  (p : C(X, A)) (q : C(X, B)) (v : C(A, B))
  (sq : v.comp p = q.comp (ContinuousMap.id X))
  (x : X) (a : A) (h : p x = a) (b : B) (hv : v a = b) (hq : q x = b)

/-- Actual base change with bijective Pi two and injective Pi one is bijective on fiber Pi one. -/
theorem mapAt_piOne_bijective
    (h1 : Function.Injective (HomotopyGroup.piMap 0 v hv))
    (h2 : Function.Bijective (HomotopyGroup.piMap 1 v hv)) :
    Function.Bijective (HomotopyGroup.piMap 0 (mapAt (ContinuousMap.id X) v sq a b hv)
      (mapAt_basepoint (ContinuousMap.id X) v sq x a x b h hq rfl hv)) := by
  let m := HomotopyGroup.piMap 0 (mapAt (ContinuousMap.id X) v sq a b hv)
    (mapAt_basepoint (ContinuousMap.id X) v sq x a x b h hq rfl hv)
  let i₁ := HomotopyGroup.piMap 0 (projection p a) (projection_basepoint p a x h)
  let i₂ := HomotopyGroup.piMap 0 (projection q b) (projection_basepoint q b x hq)
  let d₁ := connectingHom p a x h 0
  let d₂ := connectingHom q b x hq 0
  have hi (z) : i₂ (m z) = i₁ z := by
    have hh := DFunLike.congr_fun
      (projectionHom_mapAt_natural (ContinuousMap.id X) v sq x a x b h hq rfl hv 0) z
    change i₂ (m z) = HomotopyGroup.map (ContinuousMap.id X) rfl (i₁ z) at hh
    simpa only [HomotopyGroup.map_id] using hh
  have hd (z) : m (d₁ z) = d₂ (HomotopyGroup.piMap 1 v hv z) :=
    DFunLike.congr_fun (connectingHom_mapAt_natural (ContinuousMap.id X) v sq x a x b
      h hq rfl hv 0) z
  have hp (n : ℕ) (z : HomotopyGroup.Pi (n + 1) X x) :
      HomotopyGroup.piMap n v hv (HomotopyGroup.piMap n p h z) = HomotopyGroup.piMap n q hq z := by
    subst b
    have hh := homotopyGroupMap_square_natural (ContinuousMap.id X) v sq x a h z
    rw [HomotopyGroup.map_id] at hh
    exact hh
  constructor
  · apply (injective_iff_map_eq_one m).mpr
    intro z hz
    have hiz : i₁ z = 1 := by rw [← hi, hz, map_one]
    have hm : z ∈ d₁.range := by
      rw [show d₁ = connectingHom p a x h 0 from rfl,
        range_connectingHom_eq_ker_projection]
      exact hiz
    obtain ⟨c, hc⟩ := hm
    have hdc : d₂ (HomotopyGroup.piMap 1 v hv c) = 1 := by rw [← hd, hc]; exact hz
    have hr : HomotopyGroup.piMap 1 v hv c ∈ (HomotopyGroup.piMap 1 q hq).range := by
      rw [range_piMap_eq_ker_connectingHom]
      exact hdc
    obtain ⟨t, ht⟩ := hr
    have hct : c = HomotopyGroup.piMap 1 p h t := h2.injective ((hp 1 t).trans ht).symm
    have hzero : d₁ c = 1 := by
      have hr : c ∈ (HomotopyGroup.piMap 1 p h).range := ⟨t, hct.symm⟩
      rw [range_piMap_eq_ker_connectingHom] at hr
      exact hr
    rw [hc] at hzero
    exact hzero
  · intro z
    have hz : HomotopyGroup.piMap 0 p h (i₂ z) = 1 := by
      apply h1
      rw [hp, map_one]
      exact DFunLike.congr_fun (homotopyGroupMapHom_projection_comp q b x hq) z
    obtain ⟨t, ht⟩ := (mem_range_projection_iff p a x h (i₂ z)).mpr hz
    have hproj : i₂ (z * (m t)⁻¹) = 1 := by
      rw [map_mul, map_inv, hi, ht, mul_inv_cancel]
    have hr : z * (m t)⁻¹ ∈ d₂.range := by
      rw [show d₂ = connectingHom q b x hq 0 from rfl,
        range_connectingHom_eq_ker_projection]
      exact hproj
    obtain ⟨c, hc⟩ := hr
    obtain ⟨d, hd'⟩ := h2.surjective c
    refine ⟨d₁ d * t, ?_⟩
    change m (d₁ d * t) = z
    rw [map_mul, hd, hd', hc, inv_mul_cancel_right]
end BaseChange
end Topology.HomotopyFiber
