/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.Topology.Prespectrum.RelativeHomotopyReparam
import Colib.Topology.Prespectrum.RelativeHomotopyLoop
import Colib.Topology.Prespectrum.HomotopyLoop

/-! Regression checks for actual jointly continuous relative tracks and parameter-correct loops.
No compactness, Omega-equivalence, pointwise quotient or supplied cancellation is assumed. -/

noncomputable section
open CategoryTheory Topology
open scoped unitInterval
universe u
namespace Topology.LoopPrespectrum
variable {E F G : LoopPrespectrum.{u}} {f g h k : E ⟶ F}

example {H K : Homotopy f g} (J : H.RelHomotopy K) (n : ℕ) :
    Continuous (fun z : unitInterval × (unitInterval × E.space n) ↦ J.level n z) :=
  (J.level n).continuous

example {H K : Homotopy f g} (J : H.RelHomotopy K) (n : ℕ)
    (r s t : unitInterval) (x : E.space n) :
    J.level (n + 1) (r, (s, E.structureMap n x t)) =
      F.structureMap n (J.level n (r, (s, x))) t := J.comm n r s x t

example {H K : Homotopy f g} (J : H.RelHomotopy K) (n : ℕ)
    (r s : unitInterval) (x : E.space n) :
    J.level n (r, (0, x)) = f.map n x ∧
    J.level n (r, (1, x)) = g.map n x ∧
    J.level n (r, (s, E.point n)) = F.point n :=
  ⟨(J.at r).at_zero n x, (J.at r).at_one n x, (J.at r).at_point n s⟩

example {H K L : Homotopy f g} (J : H.RelHomotopy K) (J' : K.RelHomotopy L) :
    L.RelHomotopy H := (J.trans J').symm

example {H K : Homotopy f g} (J : H.RelHomotopy K) (a : F ⟶ G) :
    (H.postcomp a).RelHomotopy (K.postcomp a) := J.postcomp a

example (H : Homotopy f g) (K : Homotopy g h) (n : ℕ) (s : unitInterval)
    (x : E.space n) :
    (H.trans K).level n (s, x) =
      if hs : (s : ℝ) ≤ 1 / 2 then
        H.level n (⟨2 * s, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩, x)
      else
        K.level n
          (⟨2 * s - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le, s.2.2⟩⟩, x) :=
  ContinuousMap.HomotopyRel.trans_apply _ _ _

example (H : Homotopy f g) (K : Homotopy g h) (L : Homotopy h k) :
    ((H.trans K).trans L).RelHomotopy (H.trans (K.trans L)) :=
  Homotopy.RelHomotopy.transAssoc H K L

example (H : Homotopy f g) : (H.trans (Homotopy.refl g)).RelHomotopy H :=
  Homotopy.RelHomotopy.transRefl H

example (H : Homotopy f g) : ((Homotopy.refl f).trans H).RelHomotopy H :=
  Homotopy.RelHomotopy.reflTrans H

example (H : Homotopy f g) (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (Homotopy.RelHomotopy.reflTransSymm H).level n (r, (s, x)) =
      H.level n (⟨Path.Homotopy.reflTransSymmAux (r, s),
        Path.Homotopy.reflTransSymmAux_mem_I (r, s)⟩, x) := rfl

example (H : Homotopy f g) : (H.symm.trans H).RelHomotopy (Homotopy.refl g) :=
  (Homotopy.RelHomotopy.reflSymmTrans H).symm

example (n : ℕ) (γ : Path (E.point n) (E.point n)) (s t : unitInterval) :
    Path.toContinuousMap ((parameterLooping E).structureMap n γ t) s =
      E.structureMap n (γ s) t := rfl

example {H K : Homotopy (zeroHom E F) (zeroHom E F)} (J : H.RelHomotopy K)
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    Path.toContinuousMap (J.zeroLoopMapHomotopy.level n (r, x)) s =
      J.level n (r, (s, x)) := J.zeroLoopMapHomotopy_apply n r s x

example {H K : Homotopy (zeroHom E F) (zeroHom E F)} (J : H.RelHomotopy K)
    (n : ℕ) (r t : unitInterval) (x : E.space n) :
    J.zeroLoopMapHomotopy.level (n + 1) (r, E.structureMap n x t) =
      (parameterLooping F).structureMap n (J.zeroLoopMapHomotopy.level n (r, x)) t :=
  J.zeroLoopMapHomotopy.comm n r x t

example (H : Homotopy f f) (N : Homotopy f (zeroHom E F))
    (n : ℕ) (x : E.space n) (s : unitInterval) :
    Path.toContinuousMap ((H.nullLoopMap N).map n x) s =
      (N.symm.trans (H.trans N)).level n (s, x) := rfl

end Topology.LoopPrespectrum

example {X : Type u} [TopologicalSpace X] (x : X)
    (γ : Path (Path.refl x) (Path.refl x)) :
    Path.doubleLoopTranspose x (Path.doubleLoopTranspose x γ) = γ :=
  (Path.doubleLoopTransposeHomeomorph x).left_inv γ

-- Exact former fiber-owned continuous-map expression, now consumed from its single lower owner.
example {X : Type u} [TopologicalSpace X] (x : X) :
    Path.doubleLoopTranspose x =
      ({
        toFun β := {
          toFun s := {
            toFun t := β t s
            continuous_toFun := by fun_prop
            source' := by rw [β.source]; rfl
            target' := by rw [β.target]; rfl }
          continuous_toFun := by
            apply Path.continuous_uncurry_iff.mp
            change Continuous (fun a : unitInterval × unitInterval ↦ β a.2 a.1)
            fun_prop
          source' := by ext t; exact (β t).source
          target' := by ext t; exact (β t).target }
        continuous_toFun := by
          apply Path.continuous_uncurry_iff.mp
          apply Path.continuous_uncurry_iff.mp
          change Continuous
            (fun a : ((Path (Path.refl x) (Path.refl x) × unitInterval) × unitInterval) ↦
              a.1.1 a.2 a.1.2)
          fun_prop } : C(Path (Path.refl x) (Path.refl x), Path (Path.refl x) (Path.refl x))) := rfl
