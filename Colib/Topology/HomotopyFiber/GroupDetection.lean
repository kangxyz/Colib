/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.LESNaturality
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalence

/-! # Actual fiber maps detect positive homotopy-group equivalences

The long exact sequence is used with its original projection, connecting,
and original-map homomorphisms. The lowest step uses the actual pointed-set
connecting function, so no group structure on the zeroth homotopy set is
introduced.


Implementation provenance:
`Quillen/Topology/HomotopyFiber/GroupDetection.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w

namespace Topology.HomotopyFiber
variable {X : Type u} {Y : Type v} {B : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace B]
  (f : C(X, B)) (g : C(Y, B)) (u : C(X, Y)) (sq : g.comp u = f)
  (x : X) (b : B) (hx : f x = b)

/-- The canonical map between fibers of a map over a fixed base. -/
def mapOver : C(HomotopyFiber f b, HomotopyFiber g b) :=
  map u (ContinuousMap.id B) sq.symm b

@[simp] theorem mapOver_basepoint :
    mapOver f g u sq b (basepoint f b x hx) =
      basepoint g b (u x) ((ContinuousMap.congr_fun sq x).trans hx) :=
  map_basepoint u (ContinuousMap.id B) sq.symm x b hx

/-- Bijections of the actual fiber homotopy sets in the two neighboring
degrees imply bijectivity of the original middle homomorphism. -/
theorem piMap_bijective_of_fiberMap
    (n : ℕ)
    (hnext : Function.Bijective (HomotopyGroup.map (N := Fin (n + 1))
      (mapOver f g u sq b) (mapOver_basepoint f g u sq x b hx)))
    (hprev : Function.Injective (HomotopyGroup.map (N := Fin n)
      (mapOver f g u sq b) (mapOver_basepoint f g u sq x b hx))) :
    Function.Bijective (HomotopyGroup.piMap n u (x := x) rfl) := by
  let hy := (ContinuousMap.congr_fun sq x).trans hx
  let v := HomotopyGroup.piMap n (mapOver f g u sq b) (mapOver_basepoint f g u sq x b hx)
  let i₁ := HomotopyGroup.piMap n (projection f b) (projection_basepoint f b x hx)
  let i₂ := HomotopyGroup.piMap n (projection g b) (projection_basepoint g b (u x) hy)
  let p₁ := HomotopyGroup.piMap n f hx
  let p₂ := HomotopyGroup.piMap n g hy
  let m := HomotopyGroup.piMap n u (x := x) rfl
  have wi (a) : m (i₁ a) = i₂ (v a) :=
    homotopyGroupMap_projection_natural u (ContinuousMap.id B) sq.symm x b hx a
  have wp (a) : p₂ (m a) = p₁ a := by
    change HomotopyGroup.map g hy (HomotopyGroup.map u rfl a) = HomotopyGroup.map f hx a
    have h := homotopyGroupMap_square_natural u (ContinuousMap.id B) sq.symm x b hx a
    rw [HomotopyGroup.map_id] at h
    exact h.symm
  have wd (a) : v (connectingHom f b x hx n a) = connectingHom g b (u x) hy n a := by
    change HomotopyGroup.map (map u (ContinuousMap.id B) sq.symm b) _
      (connectingMap f b x hx (n + 1) a) = connectingMap g b (u x) hy (n + 1) a
    have h := connectingMap_natural u (ContinuousMap.id B) sq.symm x b hx (n + 1) a
    rw [HomotopyGroup.map_id] at h
    exact h
  constructor
  · apply (injective_iff_map_eq_one m).2
    intro a ha
    have hpa : p₁ a = 1 := by rw [← wp, ha, map_one]
    obtain ⟨c, hc⟩ := (mem_range_projection_iff f b x hx a).2 hpa
    have hic : i₂ (v c) = 1 := by rw [← wi, hc]; exact ha
    have hvc : v c ∈ (connectingHom g b (u x) hy n).range := by
      rw [range_connectingHom_eq_ker_projection]
      exact hic
    obtain ⟨d, hd⟩ := hvc
    have hcd : connectingHom f b x hx n d = c := hnext.injective ((wd d).trans hd)
    have hz : i₁ (connectingHom f b x hx n d) = 1 := by
      have hmem : connectingHom f b x hx n d ∈ (connectingHom f b x hx n).range := ⟨d, rfl⟩
      rw [range_connectingHom_eq_ker_projection] at hmem
      exact hmem
    rw [hcd, hc] at hz
    exact hz
  · intro a
    have hδ : connectingMap f b x hx n (p₂ a) =
        (Quotient.mk' GenLoop.const : HomotopyGroup.Pi n (HomotopyFiber f b) (basepoint f b x
          hx)) := by
      apply hprev
      change HomotopyGroup.map (map u (ContinuousMap.id B) sq.symm b) _
        (connectingMap f b x hx n (p₂ a)) = _
      rw [connectingMap_natural]
      simp only [HomotopyGroup.map_id]
      exact (mem_range_piMap_iff_connectingMap_constant g b (u x) hy n (p₂ a)).1 ⟨a, rfl⟩
    obtain ⟨c, hc⟩ := (mem_range_piMap_iff_connectingMap_constant f b x hx n (p₂ a)).2 hδ
    change p₁ c = p₂ a at hc
    have hk : p₂ (a * (m c)⁻¹) = 1 := by
      rw [map_mul, map_inv, wp, hc, mul_inv_cancel]
    obtain ⟨d, hd⟩ := (mem_range_projection_iff g b (u x) hy (a * (m c)⁻¹)).2 hk
    obtain ⟨e, he⟩ := hnext.surjective d
    change v e = d at he
    change i₂ d = a * (m c)⁻¹ at hd
    refine ⟨i₁ e * c, ?_⟩
    change m (i₁ e * c) = a
    rw [map_mul, wi, he, hd, inv_mul_cancel_right]

end Topology.HomotopyFiber
