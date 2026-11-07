/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.Equivalence
public import Colib.Topology.HomotopyFiber.LoopPrefixHomotopy

/-!
# Continuous concatenation and cancellation of cone families

These are actual homotopies of path families. They retain the original
concatenation parameters and fixed endpoints. The current consumer is the
comparison of the localized extension contraction with the capped Q cylinder.
-/
/-! Implementation source: `Quillen/Topology/Homotopy/ConcatenationFamilies.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual cone paths,
composition triangles and categorical universes are preserved under native ownership. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
open scoped Topology unitInterval
namespace Topology.ConePair
variable {X : Type u} {Z : Type v} [TopologicalSpace X] [TopologicalSpace Z]
  {x : X} {f g : C(Z, X)}

/-- The actual loop made by following the first cone and returning along the second. -/
def loopMap (A B : (ContinuousMap.const Z x).Homotopy f) : C(Z, Path x x) where
  toFun z := (A.evalAt z).trans (B.evalAt z).symm
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact Path.trans_continuous_family (fun z => A.evalAt z)
      (A.continuous.comp continuous_swap) (fun z => (B.evalAt z).symm)
      (B.continuous.comp ((unitInterval.continuous_symm.comp continuous_snd).prodMk continuous_fst))

/-- Evaluation preserves the original concatenation parameters. -/
theorem evalAt_trans (A : (ContinuousMap.const Z x).Homotopy f) (H : f.Homotopy g) (z : Z) :
    (A.trans H).evalAt z = (A.evalAt z).trans (H.evalAt z) := by
  ext t
  change A.trans H (t, z) = _
  rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
  split_ifs <;> rfl

/-- Appending the traversed part of a moving tail is jointly continuous. -/
lemma continuous_extendedPath (A : (ContinuousMap.const Z x).Homotopy f)
    (H : f.Homotopy g) :
    Continuous (fun z : (unitInterval × Z) × unitInterval =>
      ((A.evalAt z.1.2).trans (HomotopyFiber.homotopyPrefix H z.1.2 z.1.1)) z.2) := by
  refine Path.trans_continuous_family
    (fun z : unitInterval × Z => A.evalAt z.2) ?_
    (fun z : unitInterval × Z => HomotopyFiber.homotopyPrefix H z.2 z.1) ?_
  · change Continuous (fun z : (unitInterval × Z) × unitInterval => A (z.2, z.1.2))
    fun_prop
  · change Continuous (fun z : (unitInterval × Z) × unitInterval => H (z.1.1 * z.2, z.1.2))
    fun_prop

/-- The original two cones with the same continuously varying terminal segment. -/
def commonTail (A B : (ContinuousMap.const Z x).Homotopy f) (H : f.Homotopy g) :
    C(unitInterval × Z, Path x x) where
  toFun z := ((A.evalAt z.2).trans (HomotopyFiber.homotopyPrefix H z.2 z.1)).trans
    ((B.evalAt z.2).trans (HomotopyFiber.homotopyPrefix H z.2 z.1)).symm
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact Path.trans_continuous_family
      (fun z : unitInterval × Z => (A.evalAt z.2).trans
        (HomotopyFiber.homotopyPrefix H z.2 z.1)) (continuous_extendedPath A H)
      (fun z : unitInterval × Z => ((B.evalAt z.2).trans
        (HomotopyFiber.homotopyPrefix H z.2 z.1)).symm)
      (Path.symm_continuous_family _ (continuous_extendedPath B H))

/-- Remove the constant terminal segments of both cones together. -/
def unpadTail (A B : (ContinuousMap.const Z x).Homotopy f) :
    C(unitInterval × Z, Path x x) where
  toFun z := (Path.delayReflRight z.1 (A.evalAt z.2)).trans
    (Path.delayReflRight z.1 (B.evalAt z.2)).symm
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    refine Path.trans_continuous_family
      (fun z : unitInterval × Z => Path.delayReflRight z.1 (A.evalAt z.2)) ?_
      (fun z : unitInterval × Z => (Path.delayReflRight z.1 (B.evalAt z.2)).symm) ?_
    · change Continuous (fun z : (unitInterval × Z) × unitInterval =>
        A (unitInterval.qRight (z.2, z.1.1), z.1.2))
      fun_prop
    · change Continuous (fun z : (unitInterval × Z) × unitInterval =>
        B (unitInterval.qRight (unitInterval.symm z.2, z.1.1), z.1.2))
      fun_prop

/-- The untraversed common tail gives the actual two padded cones. -/
theorem commonTail_zero (A B : (ContinuousMap.const Z x).Homotopy f) (H : f.Homotopy g)
    (z : Z) : commonTail A B H (0, z) = unpadTail A B (0, z) := by
  have h (t : unitInterval) : HomotopyFiber.homotopyPrefix H z 0 t = f z := by
    change H (0 * t, z) = f z
    simp
  ext t
  change (((A.evalAt z).trans _).trans ((B.evalAt z).trans _).symm) t =
    ((Path.delayReflRight 0 (A.evalAt z)).trans
      (Path.delayReflRight 0 (B.evalAt z)).symm) t
  rw [Path.delayReflRight_zero, Path.delayReflRight_zero]
  simp only [Path.trans_apply, Path.symm_apply, Function.comp_apply, h, Path.refl_apply]

/-- The complete common tail gives the original concatenated cone pair. -/
theorem commonTail_one (A B : (ContinuousMap.const Z x).Homotopy f) (H : f.Homotopy g)
    (z : Z) : commonTail A B H (1, z) = loopMap (A.trans H) (B.trans H) z := by
  have h (t : unitInterval) : HomotopyFiber.homotopyPrefix H z 1 t = H.evalAt z t := by
    change H (1 * t, z) = H (t, z)
    simp
  ext t
  change (((A.evalAt z).trans _).trans ((B.evalAt z).trans _).symm) t =
    (((A.trans H).evalAt z).trans ((B.trans H).evalAt z).symm) t
  rw [evalAt_trans, evalAt_trans]
  simp only [Path.trans_apply, Path.symm_apply, Function.comp_apply, h]

/-- Removing both constant tails recovers the original pair. -/
theorem unpadTail_one (A B : (ContinuousMap.const Z x).Homotopy f) (z : Z) :
    unpadTail A B (1, z) = loopMap A B z := by
  change (Path.delayReflRight 1 (A.evalAt z)).trans
    (Path.delayReflRight 1 (B.evalAt z)).symm = _
  rw [Path.delayReflRight_one, Path.delayReflRight_one]
  rfl

/-- A shared terminal path cancels through a genuine homotopy of loop-valued maps. -/
def commonTailCancellation (A B : (ContinuousMap.const Z x).Homotopy f) (H : f.Homotopy g) :
    (loopMap (A.trans H) (B.trans H)).Homotopy (loopMap A B) := by
  let padded : C(Z, Path x x) := ⟨fun z => unpadTail A B (0,z),
    (unpadTail A B).continuous.comp (continuous_const.prodMk continuous_id)⟩
  let J : padded.Homotopy (loopMap (A.trans H) (B.trans H)) := {
    toContinuousMap := commonTail A B H
    map_zero_left := commonTail_zero A B H
    map_one_left := commonTail_one A B H }
  let K : padded.Homotopy (loopMap A B) := {
    toContinuousMap := unpadTail A B
    map_zero_left := fun _ => rfl
    map_one_left := unpadTail_one A B }
  exact J.symm.trans K


/-- A slice of the supplied relative homotopy retains both cone endpoints. -/
def relativeStage (A A' : (ContinuousMap.const Z x).Homotopy f)
    (J : A.toContinuousMap.HomotopyRel A'.toContinuousMap
      {z : unitInterval × Z | z.1 = 0 ∨ z.1 = 1}) (s : unitInterval) :
    (ContinuousMap.const Z x).Homotopy f where
  toFun z := J (s, z)
  continuous_toFun := J.continuous.comp (continuous_const.prodMk continuous_id)
  map_zero_left z := (J.prop s (0,z) (Or.inl rfl)).trans (A.apply_zero z)
  map_one_left z := (J.prop s (1,z) (Or.inr rfl)).trans (A.apply_one z)

/-- Relative homotopies of the two cones give a homotopy of their actual loop map. -/
def relativeLoopHomotopy (A A' B B' : (ContinuousMap.const Z x).Homotopy f)
    (JA : A.toContinuousMap.HomotopyRel A'.toContinuousMap
      {z : unitInterval × Z | z.1 = 0 ∨ z.1 = 1})
    (JB : B.toContinuousMap.HomotopyRel B'.toContinuousMap
      {z : unitInterval × Z | z.1 = 0 ∨ z.1 = 1}) :
    (loopMap A B).Homotopy (loopMap A' B') where
  toFun z := loopMap (relativeStage A A' JA z.1) (relativeStage B B' JB z.1) z.2
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    refine Path.trans_continuous_family
      (fun z : unitInterval × Z => (relativeStage A A' JA z.1).evalAt z.2) ?_
      (fun z : unitInterval × Z => ((relativeStage B B' JB z.1).evalAt z.2).symm) ?_
    · change Continuous (fun z : (unitInterval × Z) × unitInterval => JA (z.1.1, (z.2,z.1.2)))
      fun_prop
    · change Continuous (fun z : (unitInterval × Z) × unitInterval =>
        JB (z.1.1, (unitInterval.symm z.2,z.1.2)))
      fun_prop
  map_zero_left z := by
    have hA : relativeStage A A' JA 0 = A := by ext p; exact JA.apply_zero p
    have hB : relativeStage B B' JB 0 = B := by ext p; exact JB.apply_zero p
    change loopMap (relativeStage A A' JA 0) (relativeStage B B' JB 0) z = _
    rw [hA,hB]
  map_one_left z := by
    have hA : relativeStage A A' JA 1 = A' := by ext p; exact JA.apply_one p
    have hB : relativeStage B B' JB 1 = B' := by ext p; exact JB.apply_one p
    change loopMap (relativeStage A A' JA 1) (relativeStage B B' JB 1) z = _
    rw [hA,hB]

end Topology.ConePair

namespace Topology
variable {X : Type u} {Z : Type v} [TopologicalSpace X] [TopologicalSpace Z]
  {f₀ f₁ f₂ f₃ : C(Z, X)}

/-- The original path associator is continuous in the entire source family,
relative to both ends. -/
def homotopyAssociator (A : f₀.Homotopy f₁) (B : f₁.Homotopy f₂) (C : f₂.Homotopy f₃) :
    ((A.trans B).trans C).toContinuousMap.HomotopyRel
      (A.trans (B.trans C)).toContinuousMap
      {z : unitInterval × Z | z.1 = 0 ∨ z.1 = 1} where
  toFun z := Path.Homotopy.transAssoc (A.evalAt z.2.2) (B.evalAt z.2.2) (C.evalAt z.2.2)
    (z.1,z.2.1)
  continuous_toFun := by
    change Continuous (fun z : unitInterval × (unitInterval × Z) =>
      (A.trans (B.trans C))
        (⟨↑(unitInterval.symm (unitInterval.symm z.1)) * ↑z.2.1 +
          ↑(unitInterval.symm z.1) * Path.Homotopy.transAssocReparamAux z.2.1, _⟩, z.2.2))
    fun_prop
  map_zero_left z := by
    have h := (Path.Homotopy.transAssoc (A.evalAt z.2) (B.evalAt z.2) (C.evalAt z.2)).apply_zero z.1
    exact h
  map_one_left z := by
    have h := (Path.Homotopy.transAssoc (A.evalAt z.2) (B.evalAt z.2) (C.evalAt z.2)).apply_one z.1
    exact h
  prop' s z hz := by
    have h := (Path.Homotopy.transAssoc (A.evalAt z.2) (B.evalAt z.2) (C.evalAt z.2)).prop s z.1
    apply h
    rcases hz with h | h
    · exact Or.inl h
    · exact Or.inr (Set.mem_singleton_iff.mpr h)

end Topology

namespace Topology.ConePair
variable {X : Type u} {Z : Type v} [TopologicalSpace X] [TopologicalSpace Z] {x : X}

/-- Regard a homotopy between the same constant map as its actual loop-valued map. -/
def closedLoopMap (H : (ContinuousMap.const Z x).Homotopy (ContinuousMap.const Z x)) :
    C(Z, Path x x) where
  toFun z := H.evalAt z
  continuous_toFun := Path.continuous_uncurry_iff.mp (H.continuous.comp continuous_swap)

/-- A supplied endpoint-relative family induces a genuine homotopy of its closed loop maps. -/
def closedRelativeHomotopy
    (H K : (ContinuousMap.const Z x).Homotopy (ContinuousMap.const Z x))
    (J : H.toContinuousMap.HomotopyRel K.toContinuousMap
      {z : unitInterval × Z | z.1 = 0 ∨ z.1 = 1}) :
    (closedLoopMap H).Homotopy (closedLoopMap K) where
  toFun z := (relativeStage H K J z.1).evalAt z.2
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : (unitInterval × Z) × unitInterval => J (z.1.1,(z.2,z.1.2)))
    fun_prop
  map_zero_left z := by ext t; exact J.apply_zero (t,z)
  map_one_left z := by ext t; exact J.apply_one (t,z)

end Topology.ConePair
