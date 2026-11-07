/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.Topology.Homotopy.Equiv

/-! # Homotopy equivalences with a prescribed map in a homotopy-commutative square -/
/-! Implementation source: `Quillen/Topology/HomotopyEquiv/HomotopySquare.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual maps, endpoint paths,
universes and signs are retained, with native Colib dependencies. -/
@[expose] public section
namespace ContinuousMap.HomotopyEquiv
universe u v w z
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Replace the forward map of a homotopy equivalence by a homotopic map,
retaining its actual inverse and deriving both inverse homotopies. -/
def ofHomotopic (e : ContinuousMap.HomotopyEquiv X Y) (f : C(X, Y))
    (h : f.Homotopic e.toFun) : ContinuousMap.HomotopyEquiv X Y where
  toFun := f
  invFun := e.invFun
  left_inv := ((ContinuousMap.Homotopic.refl e.invFun).comp h).trans e.left_inv
  right_inv := (h.comp (ContinuousMap.Homotopic.refl e.invFun)).trans e.right_inv

variable {X' : Type w} {Y' : Type z} [TopologicalSpace X'] [TopologicalSpace Y']

/-- Three actual homotopy equivalences in a homotopy-commutative square
make the prescribed fourth map a homotopy equivalence. -/
def ofHomotopySquare (a : ContinuousMap.HomotopyEquiv X X')
    (b : ContinuousMap.HomotopyEquiv Y Y') (t : ContinuousMap.HomotopyEquiv X Y)
    (f : C(X', Y')) (h : (f.comp a.toFun).Homotopic (b.toFun.comp t.toFun)) :
    ContinuousMap.HomotopyEquiv X' Y' :=
  (a.symm.trans (t.trans b)).ofHomotopic f
    (((ContinuousMap.Homotopic.refl f).comp a.right_inv.symm).trans
      (h.comp (ContinuousMap.Homotopic.refl a.invFun)))

@[simp]
theorem ofHomotopySquare_toFun (a : ContinuousMap.HomotopyEquiv X X')
    (b : ContinuousMap.HomotopyEquiv Y Y') (t : ContinuousMap.HomotopyEquiv X Y)
    (f : C(X', Y')) (h : (f.comp a.toFun).Homotopic (b.toFun.comp t.toFun)) :
    (ofHomotopySquare a b t f h).toFun = f := rfl

end ContinuousMap.HomotopyEquiv
