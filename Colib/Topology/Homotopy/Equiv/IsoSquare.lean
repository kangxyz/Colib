/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Category.TopCat.Basic

/-! # Transport of a specified homotopy equivalence through an isomorphism square

Selected from `Quillen/CategoryTheory/TheoremA/SkeletalEquivalences.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. This generic comparison needs no
bisimplicial replacement theory. Its prescribed forward map is retained exactly.
-/
@[expose] public noncomputable section
open CategoryTheory
universe u
namespace TopCat

/-- Transport a specified homotopy equivalence along a commuting square of
actual homeomorphisms, retaining the specified forward map. -/
def homotopyEquivOfIsoSquare {A B C D : TopCat.{u}}
    (i : A ⟶ B) (j : C ⟶ D) (eA : A ≅ C) (eB : B ≅ D)
    (w : i ≫ eB.hom = eA.hom ≫ j)
    (e : ContinuousMap.HomotopyEquiv C D) (he : e.toFun = j.hom) :
    ContinuousMap.HomotopyEquiv A B := by
  let E := ((TopCat.homeoOfIso eA).toHomotopyEquiv.trans e).trans
    (TopCat.homeoOfIso eB.symm).toHomotopyEquiv
  have hE : E.toFun = i.hom := by
    apply ContinuousMap.ext
    intro x
    change eB.inv (e.toFun (eA.hom x)) = i x
    rw [he]
    have hw : eB.hom (i x) = j (eA.hom x) := ConcreteCategory.congr_hom w x
    change eB.inv (j (eA.hom x)) = i x
    rw [← hw]
    exact ConcreteCategory.congr_hom eB.hom_inv_id _
  exact { E with
    toFun := i.hom
    left_inv := by simpa only [hE] using E.left_inv
    right_inv := by simpa only [hE] using E.right_inv }

@[simp]
theorem homotopyEquivOfIsoSquare_toFun {A B C D : TopCat.{u}}
    (i : A ⟶ B) (j : C ⟶ D) (eA : A ≅ C) (eB : B ≅ D)
    (w : i ≫ eB.hom = eA.hom ≫ j)
    (e : ContinuousMap.HomotopyEquiv C D) (he : e.toFun = j.hom) :
    (homotopyEquivOfIsoSquare i j eA eB w e he).toFun = i.hom := rfl

end TopCat
