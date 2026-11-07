/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.LoopPrefixGroups

/-!
Implementation provenance:
`Quillen/Topology/HomotopyFiber/LoopPrefixBasepointNaturality.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Change of the displayed fiber basepoint in the original loop comparison

Every path between points of the actual homotopy fiber continuously varies the
original prefix map. Removing its constant suffix gives a continuous square with
that whole path as its opposite edge. Thus the corrected forward maps agree by
transport along exactly the given path in every finite degree. For a contractible
source, cancellation gives the corresponding formula for the original corrected
inverses, without a natural choice of contractions.
-/

@[expose] public section

noncomputable section

open scoped Topology unitInterval

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v

namespace Topology.HomotopyFiber

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {f : C(X, Y)} {y : Y} {z w : HomotopyFiber f y}

/-- Vary the original prefix continuously along the entire displayed fiber path. -/
def loopPrefixPathHomotopy (q : Path z w) :
    (loopPrefix f z.val.1 y (toPath f y z)).Homotopy
      (loopPrefix f w.val.1 y (toPath f y w)) where
  toFun a := loopPrefix f (q a.1).val.1 y (toPath f y (q a.1)) a.2
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact (projection f y).continuous.comp (q.continuous.comp continuous_fst)
    apply ContinuousMap.continuous_of_continuous_uncurry
    refine Path.trans_continuous_family
      (fun a : unitInterval × Path y y ↦ toPath f y (q a.1)) ?_
      (fun a : unitInterval × Path y y ↦ a.2) ?_
    · change Continuous (fun a : (unitInterval × Path y y) × unitInterval ↦
        (q a.1.1).val.2 a.2)
      fun_prop
    · fun_prop
  map_zero_left δ := by change loopPrefix f (q 0).val.1 y (toPath f y (q 0)) δ = _; rw [q.source]
  map_one_left δ := by change loopPrefix f (q 1).val.1 y (toPath f y (q 1)) δ = _; rw [q.target]

/-- The actual prefix homotopy follows the exact source coordinate of the given path. -/
@[simp] theorem loopPrefixPathHomotopy_source (q : Path z w)
    (s : unitInterval) (δ : Path y y) :
    (loopPrefixPathHomotopy q (s, δ)).val.1 = (q s).val.1 := rfl

/-- The actual prefix homotopy retains the given fiber path followed by the original loop. -/
@[simp] theorem loopPrefixPathHomotopy_path (q : Path z w)
    (s : unitInterval) (δ : Path y y) :
    (loopPrefixPathHomotopy q (s, δ)).val.2 =
      ((toPath f y (q s)).trans δ).toContinuousMap := rfl

/-- Jointly remove the constant suffix from every fiber path along the given path. -/
def loopPrefixUnitSquare (q : Path z w) : C(unitInterval × unitInterval, HomotopyFiber f y) where
  toFun a := loopPrefixUnitPath f (q a.2).val.1 y (toPath f y (q a.2)) a.1
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact (projection f y).continuous.comp (q.continuous.comp continuous_snd)
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun a : (unitInterval × unitInterval) × unitInterval ↦
      (q a.1.2).val.2 (unitInterval.qRight (a.2, a.1.1)))
    fun_prop

/-- At the padded edge, the square is the exact unit track of the prefix homotopy. -/
@[simp] theorem loopPrefixUnitSquare_zero (q : Path z w) (s : unitInterval) :
    loopPrefixUnitSquare q (0, s) = (loopPrefixPathHomotopy q).evalAt (Path.refl y) s := by
  apply Subtype.ext
  change ((q s).val.1, (Path.delayReflRight 0 (toPath f y (q s))).toContinuousMap) = _
  rw [Path.delayReflRight_zero]
  rfl

/-- At the unpadded edge, the square is the original fiber path itself. -/
@[simp] theorem loopPrefixUnitSquare_one (q : Path z w) (s : unitInterval) :
    loopPrefixUnitSquare q (1, s) = q s := by
  apply Subtype.ext
  change ((q s).val.1, (Path.delayReflRight 1 (toPath f y (q s))).toContinuousMap) = _
  rw [Path.delayReflRight_one]
  rfl

/-- The initial side is the original unit-removal path at the initial fiber point. -/
@[simp] theorem loopPrefixUnitSquare_source (q : Path z w) (s : unitInterval) :
    loopPrefixUnitSquare q (s, 0) = loopPrefixUnitPath f z.val.1 y (toPath f y z) s := by
  change loopPrefixUnitPath f (q 0).val.1 y (toPath f y (q 0)) s = _
  rw [q.source]

/-- The terminal side is the original unit-removal path at the terminal fiber point. -/
@[simp] theorem loopPrefixUnitSquare_target (q : Path z w) (s : unitInterval) :
    loopPrefixUnitSquare q (s, 1) = loopPrefixUnitPath f w.val.1 y (toPath f y w) s := by
  change loopPrefixUnitPath f (q 1).val.1 y (toPath f y (q 1)) s = _
  rw [q.target]

/-- The corrected original forward maps agree by the given fiber-basepoint transport. -/
theorem loopPrefix_pathTransport_pi (q : Path z w) (n : ℕ)
    (a : HomotopyGroup.Pi n (Path y y) (Path.refl y)) :
    pathTransport q n
      (pathTransport (loopPrefixUnitPath f z.val.1 y (toPath f y z)) n
        (HomotopyGroup.map (loopPrefix f z.val.1 y (toPath f y z)) rfl a)) =
      pathTransport (loopPrefixUnitPath f w.val.1 y (toPath f y w)) n
        (HomotopyGroup.map (loopPrefix f w.val.1 y (toPath f y w)) rfl a) := by
  have hs := pathTransport_square ((loopPrefixPathHomotopy q).evalAt (Path.refl y)) q
    (loopPrefixUnitPath f z.val.1 y (toPath f y z))
    (loopPrefixUnitPath f w.val.1 y (toPath f y w)) (loopPrefixUnitSquare q)
    (loopPrefixUnitSquare_zero q) (loopPrefixUnitSquare_one q)
    (loopPrefixUnitSquare_source q) (loopPrefixUnitSquare_target q) n
    (HomotopyGroup.map (loopPrefix f z.val.1 y (toPath f y z)) rfl a)
  exact hs.trans (congrArg
    (pathTransport (loopPrefixUnitPath f w.val.1 y (toPath f y w)) n)
    (pathTransport_homotopyGroupMap_homotopy (loopPrefixPathHomotopy q) (Path.refl y) n a))

/-- Changing the fiber basepoint along the displayed path preserves the original corrected
inverse. The proof cancels the actual forward maps and assumes no natural contraction. -/
theorem loopInverse_pathTransport_pi [ContractibleSpace X] (q : Path z w) (n : ℕ)
    (b : HomotopyGroup.Pi n (HomotopyFiber f y) z) :
    pathTransport (loopEquivOfContractibleSourcePathInverseBasepointPath
      f z.val.1 y (toPath f y z)) n
      (HomotopyGroup.map (loopEquivOfContractibleSourcePath f z.val.1 y
        (toPath f y z)).invFun rfl b) =
    pathTransport (loopEquivOfContractibleSourcePathInverseBasepointPath
      f w.val.1 y (toPath f y w)) n
      (HomotopyGroup.map (loopEquivOfContractibleSourcePath f w.val.1 y
        (toPath f y w)).invFun rfl (pathTransport q n b)) := by
  let a := pathTransport (loopEquivOfContractibleSourcePathInverseBasepointPath
    f z.val.1 y (toPath f y z)) n
    (HomotopyGroup.map (loopEquivOfContractibleSourcePath f z.val.1 y
      (toPath f y z)).invFun rfl b)
  have h := loopPrefix_pathTransport_pi q n a
  rw [loopPrefix_corrected_pi, loopPrefix_corrected_pi,
    loopEquivOfContractibleSourcePath_forward_pi] at h
  have hi := congrArg (fun c ↦
    pathTransport (loopEquivOfContractibleSourcePathInverseBasepointPath
      f w.val.1 y (toPath f y w)) n
      (HomotopyGroup.map (loopEquivOfContractibleSourcePath f w.val.1 y
        (toPath f y w)).invFun rfl c)) h
  rw [loopEquivOfContractibleSourcePath_inverse_pi] at hi
  exact hi.symm

end Topology.HomotopyFiber
