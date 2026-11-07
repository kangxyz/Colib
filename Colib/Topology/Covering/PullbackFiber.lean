/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Covering.Pullback
public import Colib.Topology.Covering.HomotopyGroups
public import Colib.Topology.HomotopyFiber.BasedLESNaturality
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalence

/-!
# The original homotopy fibers of a covering pullback

The literal strict pullback square induces its actual `mapAt` map from the
homotopy fiber of the second projection to the homotopy fiber of the original
map. When the supplied covering total space is simply connected, this actual
map is bijective on Pi one. The proof uses original long-exact-sequence maps,
the exact first-projection kernel, and the covering maps' original Pi-two
bijections. The projection and connecting squares are retained explicitly.

No connectedness or simple-connectedness of the pullback is assumed. No
surjectivity hypothesis on the original Pi-one map is needed for this fiber
comparison. All three spaces may have independent universes.
-/
/-! Implementation source: `Quillen/Topology/Covering/PullbackFiber.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual matching-pair subtype,
map of path-space fibers and canonical projection/connecting equations are retained. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w
open IsCoveringMap
open scoped Topology unitInterval
namespace Topology.Covering.Pullback
variable {X : Type u} {Y : Type v} {E : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace E]
  (f : C(X, Y)) (q : C(E, Y)) (hq : IsCoveringMap q)
  (z₀ : Space f q)

/-- The actual map of homotopy fibers induced by the original strict pullback square. -/
def fiberMap : C(HomotopyFiber (lift f q) z₀.val.2, HomotopyFiber f (q z₀.val.2)) :=
  HomotopyFiber.mapAt (projection f q) q (square f q) z₀.val.2 (q z₀.val.2) rfl

/-- The actual fiber map retains the supplied matching pair as its original basepoint. -/
theorem fiberMap_basepoint :
    fiberMap f q z₀ (HomotopyFiber.basepoint (lift f q) z₀.val.2 z₀ rfl) =
      HomotopyFiber.basepoint f (q z₀.val.2) z₀.val.1 z₀.property :=
  HomotopyFiber.mapAt_basepoint (projection f q) q (square f q)
    z₀ z₀.val.2 z₀.val.1 (q z₀.val.2) rfl z₀.property rfl rfl

/-- The induced Pi-one map uses the literal fiber map and exact basepoint equality. -/
def fiberPiOneMap :
    HomotopyGroup.Pi 1 (HomotopyFiber (lift f q) z₀.val.2)
        (HomotopyFiber.basepoint (lift f q) z₀.val.2 z₀ rfl) →*
      HomotopyGroup.Pi 1 (HomotopyFiber f (q z₀.val.2))
        (HomotopyFiber.basepoint f (q z₀.val.2) z₀.val.1 z₀.property) :=
  HomotopyGroup.piMap 0 (fiberMap f q z₀) (fiberMap_basepoint f q z₀)

/-- The actual fiber Pi-one map preserves the original projection equation. -/
theorem fiberPiOneMap_projection :
    (HomotopyGroup.piMap 0 (HomotopyFiber.projection f (q z₀.val.2))
      (HomotopyFiber.projection_basepoint f (q z₀.val.2) z₀.val.1 z₀.property)).comp
        (fiberPiOneMap f q z₀) =
    (HomotopyGroup.piMap 0 (projection f q) (x := z₀) rfl).comp
      (HomotopyGroup.piMap 0 (HomotopyFiber.projection (lift f q) z₀.val.2)
        (HomotopyFiber.projection_basepoint (lift f q) z₀.val.2 z₀ rfl)) :=
  HomotopyFiber.projectionHom_mapAt_natural (projection f q) q (square f q)
    z₀ z₀.val.2 z₀.val.1 (q z₀.val.2) rfl z₀.property rfl rfl 0

/-- The actual fiber Pi-one map preserves the original degree-two connecting equation. -/
theorem fiberPiOneMap_connecting :
    (fiberPiOneMap f q z₀).comp (HomotopyFiber.connectingHom (lift f q) z₀.val.2 z₀ rfl 0) =
      (HomotopyFiber.connectingHom f (q z₀.val.2) z₀.val.1 z₀.property 0).comp
        (HomotopyGroup.piMap 1 q (x := z₀.val.2) rfl) :=
  HomotopyFiber.connectingHom_mapAt_natural (projection f q) q (square f q)
    z₀ z₀.val.2 z₀.val.1 (q z₀.val.2) rfl z₀.property rfl rfl 0

/-- The actual total and base maps retain the original strict square in every positive degree. -/
theorem piMap_square (n : ℕ) (a : HomotopyGroup.Pi (n + 1) (Space f q) z₀) :
    HomotopyGroup.piMap n q rfl (HomotopyGroup.piMap n (lift f q) rfl a) =
      HomotopyGroup.piMap n f z₀.property (HomotopyGroup.piMap n (projection f q) rfl a) := by
  exact (HomotopyGroup.map_comp (lift f q) rfl q rfl a).symm.trans
    ((congrFun (homotopyGroupMap_congr (square f q) rfl z₀.property) a).trans
      (HomotopyGroup.map_comp (projection f q) rfl f z₀.property a))

variable [SimplyConnectedSpace E]

include hq in
/-- The original fiber-map Pi one is bijective, without assuming the pullback simply connected. -/
theorem fiberPiOneMap_bijective : Function.Bijective (fiberPiOneMap f q z₀) := by
  let m := fiberPiOneMap f q z₀
  let p₁ := HomotopyGroup.piMap 0 (projection f q) (x := z₀) rfl
  let p₂ := HomotopyGroup.piMap 1 (projection f q) (x := z₀) rfl
  let q₂ := HomotopyGroup.piMap 1 q (x := z₀.val.2) rfl
  let k₁ := HomotopyGroup.piMap 0 (lift f q) (x := z₀) rfl
  let k₂ := HomotopyGroup.piMap 1 (lift f q) (x := z₀) rfl
  let f₁ := HomotopyGroup.piMap 0 f z₀.property
  let f₂ := HomotopyGroup.piMap 1 f z₀.property
  let iP := HomotopyGroup.piMap 0 (HomotopyFiber.projection (lift f q) z₀.val.2)
    (HomotopyFiber.projection_basepoint (lift f q) z₀.val.2 z₀ rfl)
  let iX := HomotopyGroup.piMap 0 (HomotopyFiber.projection f (q z₀.val.2))
    (HomotopyFiber.projection_basepoint f (q z₀.val.2) z₀.val.1 z₀.property)
  let dP := HomotopyFiber.connectingHom (lift f q) z₀.val.2 z₀ rfl 0
  let dX := HomotopyFiber.connectingHom f (q z₀.val.2) z₀.val.1 z₀.property 0
  have hp₁ : Function.Injective p₁ := piOne_projection_injective f q hq z₀
  have hp₂ : Function.Surjective p₂ :=
    (homotopyGroupMap_projection_bijective (projection_isCoveringMap f q hq)
      (Fin 2) z₀ rfl).surjective
  have hq₂ : Function.Bijective q₂ :=
    homotopyGroupMap_projection_bijective hq (Fin 2) z₀.val.2 rfl
  have hi (a) : iX (m a) = p₁ (iP a) :=
    DFunLike.congr_fun (fiberPiOneMap_projection f q z₀) a
  have hd (a) : m (dP a) = dX (q₂ a) :=
    DFunLike.congr_fun (fiberPiOneMap_connecting f q z₀) a
  constructor
  · apply (injective_iff_map_eq_one m).mpr
    intro a ha
    have hproj : iP a = 1 := by
      apply hp₁
      rw [map_one, ← hi, ha, map_one]
    have hr : a ∈ dP.range := by
      rw [show dP = HomotopyFiber.connectingHom (lift f q) z₀.val.2 z₀ rfl 0 from rfl,
        HomotopyFiber.range_connectingHom_eq_ker_projection]
      exact hproj
    obtain ⟨c, hc⟩ := hr
    have hδ : dX (q₂ c) = 1 := by rw [← hd, hc]; exact ha
    have hfr : q₂ c ∈ f₂.range := by
      rw [show f₂ = HomotopyGroup.piMap 1 f z₀.property from rfl,
        HomotopyFiber.range_piMap_eq_ker_connectingHom]
      exact hδ
    obtain ⟨t, ht⟩ := hfr
    obtain ⟨s, hs⟩ := hp₂ t
    have hks : k₂ s = c := by
      apply hq₂.injective
      exact (piMap_square f q z₀ 1 s).trans ((congrArg f₂ hs).trans ht)
    have hz : dP c = 1 := by
      have hkr : c ∈ k₂.range := ⟨s, hks⟩
      rw [show k₂ = HomotopyGroup.piMap 1 (lift f q) (x := z₀) rfl from rfl,
        HomotopyFiber.range_piMap_eq_ker_connectingHom] at hkr
      exact hkr
    rw [hc] at hz
    exact hz
  · intro a
    have hix : iX a ∈ f₁.ker := by
      exact DFunLike.congr_fun
        (HomotopyFiber.homotopyGroupMapHom_projection_comp f
          (q z₀.val.2) z₀.val.1 z₀.property) a
    have hpr : iX a ∈ p₁.range := (piOne_projection_range f q hq z₀).ge hix
    obtain ⟨b, hb⟩ := hpr
    have hkb : k₁ b = 1 := by
      apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
      exact Subsingleton.elim _ _
    obtain ⟨c, hc⟩ := (HomotopyFiber.mem_range_projection_iff
      (lift f q) z₀.val.2 z₀ rfl b).mpr hkb
    have hdiff : iX (a * (m c)⁻¹) = 1 := by
      rw [map_mul, map_inv, hi, hc, hb, mul_inv_cancel]
    have hdr : a * (m c)⁻¹ ∈ dX.range := by
      rw [show dX = HomotopyFiber.connectingHom f (q z₀.val.2)
        z₀.val.1 z₀.property 0 from rfl, HomotopyFiber.range_connectingHom_eq_ker_projection]
      exact hdiff
    obtain ⟨t, ht⟩ := hdr
    obtain ⟨s, hs⟩ := hq₂.surjective t
    refine ⟨dP s * c, ?_⟩
    change m (dP s * c) = a
    rw [map_mul, hd, hs, ht, inv_mul_cancel_right]

/-- The original actual map of fibers gives the resulting fundamental-group equivalence. -/
def fiberPiOneEquiv :
    HomotopyGroup.Pi 1 (HomotopyFiber (lift f q) z₀.val.2)
        (HomotopyFiber.basepoint (lift f q) z₀.val.2 z₀ rfl) ≃*
      HomotopyGroup.Pi 1 (HomotopyFiber f (q z₀.val.2))
        (HomotopyFiber.basepoint f (q z₀.val.2) z₀.val.1 z₀.property) :=
  MulEquiv.ofBijective (fiberPiOneMap f q z₀) (fiberPiOneMap_bijective f q hq z₀)

/-- The actual fiber equivalence retains precisely the original mapAt map on Pi one. -/
theorem fiberPiOneEquiv_apply
    (a : HomotopyGroup.Pi 1 (HomotopyFiber (lift f q) z₀.val.2)
      (HomotopyFiber.basepoint (lift f q) z₀.val.2 z₀ rfl)) :
    fiberPiOneEquiv f q hq z₀ a = fiberPiOneMap f q z₀ a := rfl

end Topology.Covering.Pullback
