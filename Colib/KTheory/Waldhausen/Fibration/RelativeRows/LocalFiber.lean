/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Fibration.RelativeRows.Realization
public import Colib.Topology.Realization.SplitFiber

/-! # The original relative-row fiber inclusion in every finite dimension

Genuine relative additivity and the strict original split triangle identify
the actual constant-path fiber inclusion on all finite based homotopy sets,
including dimension zero. Its projection is exactly the original tail map.
This is a degreewise statement; the global diagonal fiber step is separate.


Implementation provenance:
`Quillen/Waldhausen/Fibration/RelativeRows/LocalFiber.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology
open CategoryTheory Opposite
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.RelativeRows
variable {C : Type u} [Category.{u} C] {V : Structure C}
  (N : NestedWeakEquivalences V) (n : SimplexCategory)

/-- The actual row projection used by the original split fiber calculus. -/
def rowFiberProjection : C(|(relativeSRows N).obj (op n)|,
    |(ordinarySRows (acyclicStructure N)).obj (op n)|) :=
  SSet.SplitRealizationFiber.projection (firstTailSSet N n)

/-- The entire row projection is exactly the original realized tail map. -/
@[simp] theorem rowFiberProjection_eq :
    rowFiberProjection N n = (SSet.toTop.map ((tailSRows N).app (op n))).hom := by
  change (SSet.toTop.map (firstTailSSet N n) ≫
    SSet.toTop.map (CartesianMonoidalCategory.snd _ _)).hom = _
  rw [← Functor.map_comp, firstTailSSet_snd]

/-- The original fiber section with its actual constant chosen-zero path. -/
def rowFiberInclusion : C(|sSet V.cof V.weq|,
    HomotopyFiber (rowFiberProjection N n) (SSet.realizationPoint (tailZeroVertex N n))) :=
  SSet.SplitRealizationFiber.inclusion (firstTailSSet N n) ((fiberSRows N).app (op n))
    (tailZeroVertex N n) (fiber_firstTailSSet N n)

/-- Both original source and path coordinates are retained literally. -/
@[simp] theorem rowFiberInclusion_apply (x : |sSet V.cof V.weq|) :
    (rowFiberInclusion N n x).1 =
      (SSet.toTop.map ((fiberSRows N).app (op n)) x,
        ContinuousMap.const _ (SSet.realizationPoint (tailZeroVertex N n))) := rfl

/-- Genuine relative additivity proves bijectivity on every original finite
based homotopy set, including dimension zero. -/
theorem rowFiberInclusion_bijective (x : |sSet V.cof V.weq|) (k : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin k) (rowFiberInclusion N n) (x := x) rfl) :=
  SSet.SplitRealizationFiber.inclusion_bijective (firstTailSSet N n) ((fiberSRows N).app (op n))
    (tailZeroVertex N n) (fiber_firstTailSSet N n)
    (firstTailSSetRealizationHomotopyEquiv N n)
    (firstTailSSetRealizationHomotopyEquiv_toFun N n) x k

end CategoryTheory.Waldhausen.Fibration.RelativeRows
