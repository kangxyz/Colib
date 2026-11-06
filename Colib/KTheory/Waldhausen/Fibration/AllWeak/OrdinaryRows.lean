/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Fibration.AllWeak.AcyclicEquivalence
public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.Simplicial
public import Colib.CategoryTheory.Waldhausen.Rows.Functoriality
public import Colib.CategoryTheory.Waldhausen.Rows.PostcomposeExact

/-! # The original all-acyclic double-S base identification

The actual inverse exact inclusion and lift give strictly inverse maps on
ordinarySRows. Both the original row diagrams and every ordinal restriction
are retained. The common object/hom universe is explicit for these S-maps.


Implementation provenance:
`Quillen/Waldhausen/Fibration/AllWeak/OrdinaryRows.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.AllWeak
variable {C : Type u} [SmallCategory C] (W : Structure C)

/-- Apply the original exact acyclic inclusion to every original ordinary row. -/
def ordinaryRowsInclusion :
    RelativeRows.ordinarySRows (acyclicStructure (nested W)) ⟶ RelativeRows.ordinarySRows W where
  app n := sSetMap (QuotientRows.postcompose_exact (acyclicStructure (nested W)) W
    (Fibration.acyclicInclusion_exact (nested W)) n.unop)
  naturality n m α := by
    ext k F : 4
    rfl

/-- Insert the trivial acyclicity witnesses in every original ordinary row. -/
def ordinaryRowsLift : RelativeRows.ordinarySRows W ⟶
    RelativeRows.ordinarySRows (acyclicStructure (nested W)) where
  app n := sSetMap (QuotientRows.postcompose_exact W (acyclicStructure (nested W))
    (acyclicLift_exact W) n.unop)
  naturality n m α := by
    ext k F : 4
    rfl

/-- The actual two ordinarySRows diagrams are naturally isomorphic. -/
def ordinaryRowsIso :
    RelativeRows.ordinarySRows (acyclicStructure (nested W)) ≅ RelativeRows.ordinarySRows W where
  hom := ordinaryRowsInclusion W
  inv := ordinaryRowsLift W
  hom_inv_id := by
    ext n k F : 5
    rfl
  inv_hom_id := by
    ext n k F : 5
    rfl

/-- Each original nested component is literally its unchanged underlying object. -/
@[simp] theorem ordinaryRowsInclusion_obj (n k : SimplexCategory)
    (F : ((RelativeRows.ordinarySRows (acyclicStructure (nested W))).obj (op n)).obj (op k))
    (q : Grid k) (p : Interval n) :
    (((((ordinaryRowsInclusion W).app (op n)).app (op k) F).val.obj q).obj.obj p) =
      ((F.val.obj q).obj.obj p).obj := rfl

@[simp] theorem ordinaryRowsLift_obj (n k : SimplexCategory)
    (F : ((RelativeRows.ordinarySRows W).obj (op n)).obj (op k))
    (q : Grid k) (p : Interval n) :
    ((((((ordinaryRowsLift W).app (op n)).app (op k) F).val.obj q).obj.obj p).obj) =
      (F.val.obj q).obj.obj p := rfl

/-- The actual original all-zero simplex is retained in both S directions. -/
@[simp] theorem ordinaryRowsInclusion_zero (n k : SimplexCategory) :
    (((ordinaryRowsInclusion W).app (op n)).app (op k)
      (zeroSimplex (QuotientRows.waldhausenStructure (acyclicStructure (nested W)) n).cof
        (QuotientRows.waldhausenStructure (acyclicStructure (nested W)) n).weq
        (QuotientRows.zero (acyclicStructure (nested W)) n)
        (QuotientRows.isZero (acyclicStructure (nested W)) n) (op k))) =
      zeroSimplex (QuotientRows.waldhausenStructure W n).cof
        (QuotientRows.waldhausenStructure W n).weq
        (QuotientRows.zero W n) (QuotientRows.isZero W n) (op k) := by
  apply Subtype.ext
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The original double-S diagonals are isomorphic, by the original exact maps. -/
def ordinaryDiagonalIso :
    SSet.diagonalSSet (RelativeRows.ordinarySRows (acyclicStructure (nested W))) ≅
      SSet.diagonalSSet (RelativeRows.ordinarySRows W) where
  hom := SSet.diagonalMap (ordinaryRowsInclusion W)
  inv := SSet.diagonalMap (ordinaryRowsLift W)
  hom_inv_id := by ext n F : 4; rfl
  inv_hom_id := by ext n F : 4; rfl

@[simp] theorem ordinaryDiagonalIso_hom :
    (ordinaryDiagonalIso W).hom = SSet.diagonalMap (ordinaryRowsInclusion W) := rfl
end CategoryTheory.Waldhausen.Fibration.AllWeak
