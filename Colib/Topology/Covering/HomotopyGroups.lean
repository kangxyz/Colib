/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Homotopy.Cube.Connectivity
public import Colib.Topology.Homotopy.HomotopyGroup.Map
public import Mathlib.Topology.Homotopy.Lifting

/-!
# The actual covering projection on higher homotopy groups

Unique lifting acts directly on Mathlib's generalized loops, in their original
cube domain. Path connectedness of the actual boundary forces the lifted
boundary to be constant. Relative covering-homotopy lifting detects precisely
the original quotient relation. No alternative spherical model is introduced.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval

namespace IsCoveringMap

universe u v w
variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
  {p : E → B} (hp : IsCoveringMap p)

/-- The zero corner of a nonempty cube lies in its actual boundary. -/
theorem cube_zero_mem_boundary (N : Type w) [Nonempty N] :
    (fun _ : N => (0 : unitInterval)) ∈ Cube.boundary N :=
  ⟨Classical.arbitrary N, Or.inl rfl⟩

/-- The parameter contraction used in the actual covering-homotopy lift. -/
def cubeContractionMap (N : Type w) (s : C(N → unitInterval, B)) :
    C(unitInterval × (N → unitInterval), B) :=
  s.comp ⟨fun z i => z.1 * z.2 i, by
    apply continuous_pi
    intro i
    exact ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd))).subtype_mk _⟩

/-- Covering-homotopy lifting on the original cubical parameter space. -/
def cubeLift (N : Type w) (s : C(N → unitInterval, B)) (e : E)
    (he : p e = s (fun _ => 0)) : C(N → unitInterval, E) :=
  (hp.liftHomotopy (cubeContractionMap N s) (.const _ e)
    (fun x => by simpa [cubeContractionMap] using he.symm)).comp
      ⟨fun x => (1, x), by fun_prop⟩

/-- The cubical lift starts at the specified lift of the zero corner. -/
theorem cubeLift_zero (N : Type w) (s : C(N → unitInterval, B)) (e : E)
    (he : p e = s (fun _ => 0)) : hp.cubeLift N s e he (fun _ => 0) = e := by
  have hL : ContinuousMap.const unitInterval e =
      hp.liftPath ((cubeContractionMap N s).comp
        ((ContinuousMap.id unitInterval).prodMk (.const _ (fun _ => 0)))) e
        (by simpa [cubeContractionMap] using he.symm) := by
    apply (hp.eq_liftPath_iff' _).mpr
    refine ⟨?_, rfl⟩
    funext t
    simpa [cubeContractionMap] using he
  exact (ContinuousMap.congr_fun hL 1).symm

/-- The cube lift projects exactly to its original parameter map. -/
theorem cubeLift_lifts (N : Type w) (s : C(N → unitInterval, B)) (e : E)
    (he : p e = s (fun _ => 0)) : p ∘ hp.cubeLift N s e he = s := by
  funext x
  have h := congr_fun (hp.liftHomotopy_lifts (cubeContractionMap N s) (.const _ e)
    (fun x => by simpa [cubeContractionMap] using he.symm)) (1, x)
  simpa [cubeLift, cubeContractionMap] using h

/-- A generalized loop in at least two directions lifts to an actual generalized loop. -/
def genLoopLift (N : Type w) [Nontrivial N] (e : E) {b : B} (he : p e = b)
    (s : GenLoop N B b) : GenLoop N E e := by
  have hzero := cube_zero_mem_boundary N
  let hbase := he.trans (s.property _ hzero).symm
  let τ := hp.cubeLift N s.val e hbase
  refine ⟨τ, fun x hx => ?_⟩
  have hproj (t : N → unitInterval) : p (τ t) = s t :=
    congr_fun (hp.cubeLift_lifts N s.val e hbase) t
  have hconst : τ x = τ (fun _ => 0) :=
    hp.constOn_of_comp (Cube.isPathConnected_boundary N).isConnected.isPreconnected
      τ.continuous.continuousOn
      (fun a ha a' ha' => (hproj a).trans
        ((s.property a ha).trans ((s.property a' ha').symm.trans (hproj a').symm)))
      hx hzero
  exact hconst.trans (hp.cubeLift_zero N s.val e hbase)

/-- The lifted generalized loop projects to the original loop, before taking classes. -/
@[simp]
theorem postcomp_genLoopLift (N : Type w) [Nontrivial N] (e : E) {b : B}
    (he : p e = b) (s : GenLoop N B b) :
    GenLoop.postcomp ⟨p, hp.continuous⟩ he (hp.genLoopLift N e he s) = s := by
  ext t
  exact congr_fun (hp.cubeLift_lifts N s.val e
    (he.trans (s.property _ (cube_zero_mem_boundary N)).symm)) t

/-- The original covering map is bijective on actual generalized-loop classes
when the indexing type has two distinct elements. -/
theorem homotopyGroupMap_projection_bijective (N : Type w) [Nontrivial N]
    (e : E) {b : B} (he : p e = b) :
    Function.Bijective (HomotopyGroup.map (N := N) ⟨p, hp.continuous⟩ he) := by
  let := Cube.contractibleSpace N
  constructor
  · intro a a'
    refine Quotient.inductionOn₂ a a' ?_
    intro s s' h
    apply Quotient.sound
    apply (hp.homotopicRel_iff_comp
      ⟨fun _ => 0, cube_zero_mem_boundary N,
        (s.property _ (cube_zero_mem_boundary N)).trans
          (s'.property _ (cube_zero_mem_boundary N)).symm⟩).mpr
    exact Quotient.exact h
  · intro a
    obtain ⟨s⟩ := a
    refine ⟨⟦hp.genLoopLift N e he s⟧, ?_⟩
    change Quotient.mk' (GenLoop.postcomp ⟨p, hp.continuous⟩ he
      (hp.genLoopLift N e he s)) = Quotient.mk' s
    exact congrArg Quotient.mk' (hp.postcomp_genLoopLift N e he s)

/-- In every degree at least two, the equivalence is exactly the original projection. -/
def piProjectionEquiv (m : ℕ) (e : E) {b : B} (he : p e = b) :
    HomotopyGroup.Pi (m + 2) E e ≃* HomotopyGroup.Pi (m + 2) B b :=
  MulEquiv.ofBijective (HomotopyGroup.piMap (m + 1) ⟨p, hp.continuous⟩ he)
    (hp.homotopyGroupMap_projection_bijective (Fin (m + 2)) e he)

@[simp]
theorem piProjectionEquiv_apply (m : ℕ) (e : E) {b : B} (he : p e = b)
    (a : HomotopyGroup.Pi (m + 2) E e) :
    hp.piProjectionEquiv m e he a = HomotopyGroup.piMap (m + 1) ⟨p, hp.continuous⟩ he a := rfl

end IsCoveringMap
