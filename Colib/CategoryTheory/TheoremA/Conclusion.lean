/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremA.Augmentations

/-! Source: Quillen/CategoryTheory/TheoremA/Conclusion.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Native topology lower owners are reused. -/

/-!
# Canonical-map assembly for the Theorem A argument

These are general homotopy-equivalence algebra lemmas, followed by their
application to the two constructed diagonal augmentations. No assertion
that the diagonal augmentations are equivalences is introduced: the missing
skeletal invariance theorem must provide those inputs independently.
-/
@[expose] public section

noncomputable section

open SSet TopCat CategoryTheory
open scoped Simplicial Topology

universe u

namespace CategoryTheory.TheoremA

section Topology

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Replacing the forward map of a homotopy equivalence by a homotopic map
preserves homotopy equivalence and keeps the supplied map exactly. -/
def homotopyEquivWithMap (e : ContinuousMap.HomotopyEquiv X Y) (f : C(X, Y))
    (h : f.Homotopic e.toFun) : ContinuousMap.HomotopyEquiv X Y where
  toFun := f
  invFun := e.invFun
  left_inv := (ContinuousMap.Homotopic.comp (.refl e.invFun) h).trans e.left_inv
  right_inv := (ContinuousMap.Homotopic.comp h (.refl e.invFun)).trans e.right_inv

/-- The homotopy-commuting triangle form of two-out-of-three, with the given
map as the exact forward map of the resulting equivalence. -/
def homotopyEquivOfTriangle (s : ContinuousMap.HomotopyEquiv X Y)
    (t : ContinuousMap.HomotopyEquiv X Z) (f : C(Y, Z))
    (h : (f.comp s.toFun).Homotopic t.toFun) : ContinuousMap.HomotopyEquiv Y Z :=
  homotopyEquivWithMap (s.symm.trans t) f <|
    (show f.Homotopic (f.comp (s.toFun.comp s.invFun)) from by
      simpa using ContinuousMap.Homotopic.comp (.refl f) s.right_inv.symm).trans
      (ContinuousMap.Homotopic.comp h (.refl s.invFun))

@[simp]
theorem homotopyEquivOfTriangle_toFun (s : ContinuousMap.HomotopyEquiv X Y)
    (t : ContinuousMap.HomotopyEquiv X Z) (f : C(Y, Z))
    (h : (f.comp s.toFun).Homotopic t.toFun) :
    (homotopyEquivOfTriangle s t f h).toFun = f := rfl

end Topology

variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- Once actual equivalences for the two diagonal augmentations have been
proved by realization invariance, their canonical comparison gives the
required equivalence whose forward map is exactly `|N F|`.

This is the final assembly lemma, not the contractible-comma criterion. -/
def canonicalEquivalenceFromAugmentations
    (s : ContinuousMap.HomotopyEquiv
      |replacementDiagonal (commaNerveDiagram F)| (ClassifyingSpace C))
    (t : ContinuousMap.HomotopyEquiv
      |replacementDiagonal (commaNerveDiagram F)| (ClassifyingSpace D))
    (hs : s.toFun = (SSet.toTop.map (diagonalSourceMap F)).hom)
    (ht : t.toFun = (SSet.toTop.map (replacementBaseMap (commaNerveDiagram F))).hom) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace C) (ClassifyingSpace D) :=
  homotopyEquivOfTriangle s t (classifyingSpaceMap F).hom (by
    rw [hs, ht]
    exact ⟨diagonalAugmentationHomotopy F⟩)

@[simp]
theorem canonicalEquivalenceFromAugmentations_toFun
    (s : ContinuousMap.HomotopyEquiv
      |replacementDiagonal (commaNerveDiagram F)| (ClassifyingSpace C))
    (t : ContinuousMap.HomotopyEquiv
      |replacementDiagonal (commaNerveDiagram F)| (ClassifyingSpace D))
    (hs : s.toFun = (SSet.toTop.map (diagonalSourceMap F)).hom)
    (ht : t.toFun = (SSet.toTop.map (replacementBaseMap (commaNerveDiagram F))).hom) :
    (canonicalEquivalenceFromAugmentations F s t hs ht).toFun = (classifyingSpaceMap F).hom := rfl

end CategoryTheory.TheoremA
