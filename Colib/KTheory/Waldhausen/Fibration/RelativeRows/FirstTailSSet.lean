/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.Simplicial
public import Colib.CategoryTheory.Waldhausen.Product.SSet
public import Colib.KTheory.Waldhausen.Connected
public import Colib.Topology.Realization.ProductFiber

/-! # The original degreewise first/tail product map and strict split triangle

The target is the genuine simplicial product. The second projection is the
original tail map, and the split triangle is the actual constant-vertex
section required by the local homotopy-fiber calculus. No realization
homotopy equivalence of this map is assumed or concluded here.


Implementation provenance:
`Quillen/Waldhausen/Fibration/RelativeRows/FirstTailSSet.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.RelativeRows
variable {C : Type u} [Category.{u} C] {V : Structure C} (N : NestedWeakEquivalences V)

/-- The original degreewise first/tail functor followed by the genuine product S-isomorphism. -/
def firstTailSSet (n : SimplexCategory) : (relativeSRows N).obj (op n) ⟶
    sSet V.cof V.weq ⊗ (ordinarySRows (acyclicStructure N)).obj (op n) :=
  sSetMap (firstTail_exact N n) ≫ Product.comparison V
    (QuotientRows.waldhausenStructure (acyclicStructure N) n)

/-- The original second projection is exactly the original acyclic-tail S-map. -/
@[simp] theorem firstTailSSet_snd (n : SimplexCategory) :
    firstTailSSet N n ≫ snd _ _ = (tailSRows N).app (op n) := by
  ext k X
  rfl

/-- The original first projection is exactly the degreewise first-object S-map. -/
@[simp] theorem firstTailSSet_fst (n : SimplexCategory) :
    firstTailSSet N n ≫ fst _ _ = sSetMap (first_exact N n) := by
  ext k X
  rfl

/-- The original actual chosen zero vertex in the tail S-construction. -/
def tailZeroVertex (n : SimplexCategory) : ((ordinarySRows (acyclicStructure N)).obj (op n)) _⦋0⦌ :=
  zeroSimplex (QuotientRows.waldhausenStructure (acyclicStructure N) n).cof
    (QuotientRows.waldhausenStructure (acyclicStructure N) n).weq
    (QuotientRows.zero (acyclicStructure N) n) (QuotientRows.isZero (acyclicStructure N) n) (op ⦋0⦌)

/-- The split triangle is the literal original constant-vertex product section. -/
@[simp] theorem fiber_firstTailSSet (n : SimplexCategory) :
    (fiberSRows N).app (op n) ≫ firstTailSSet N n =
      SSet.ProductRealization.vertexSection (sSet V.cof V.weq)
        ((ordinarySRows (acyclicStructure N)).obj (op n)) (tailZeroVertex N n) := by
  ext k X <;> rfl

/-- Every actual inner relative-row S-realization is genuinely path-connected. -/
instance relativeSRows_pathConnected (n : SimplexCategory) :
    PathConnectedSpace |(relativeSRows N).obj (op n)| :=
  inferInstanceAs (PathConnectedSpace (waldhausenStructure N n).Delooping)

/-- Every actual inner acyclic-tail-row S-realization is genuinely path-connected. -/
instance tailSRows_pathConnected (n : SimplexCategory) :
    PathConnectedSpace |(ordinarySRows (acyclicStructure N)).obj (op n)| :=
  inferInstanceAs (PathConnectedSpace (QuotientRows.waldhausenStructure (acyclicStructure N)
    n).Delooping)

end CategoryTheory.Waldhausen.Fibration.RelativeRows
