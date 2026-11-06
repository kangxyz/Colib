/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Approximation.FiniteReplacement
public import Colib.Topology.ClassifyingSpace.Contraction

/-!
# Actual weak-equivalence categories of finite flags

The morphisms here are pointwise weak-equivalence natural transformations,
not natural isomorphisms. Functorial factorization constructs homotopy
inverses on these categories of flags when cofibrations are enlarged.
Both natural comparison transformations and the homotopies of actual
classifying spaces are constructed. Passing to quotient rows and the
simplicial diagonal is separate.

Implementation provenance: `Quillen/Waldhausen/Approximation/WeakFlags.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, hypotheses,
chosen zero objects and universe parameters are retained.
-/
@[expose] public section


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Waldhausen

variable {C : Type u} [Category.{v} C]

/-- A finite flag starts at a zero object and all its forward maps are cofibrations.
The weak-equivalence parameter specifies its morphism category below. -/
structure WeakFlag (cof weq : MorphismProperty C) (n : ℕ) where
  /-- The underlying sequence of `n` composable arrows, starting at a zero object and with every
  forward map in `cof`. -/
  diagram : ComposableArrows C n
  zero : IsZero (diagram.obj 0)
  cofibration {i j : Fin (n + 1)} (f : i ⟶ j) : cof (diagram.map f)

namespace WeakFlag

variable {cof weq : MorphismProperty C} {n : ℕ} [weq.IsMultiplicative]

instance : Category (WeakFlag cof weq n) where
  Hom F G := { α : F.diagram ⟶ G.diagram // ∀ i, weq (α.app i) }
  id F := ⟨𝟙 F.diagram, fun _ ↦ weq.id_mem _⟩
  comp α β := ⟨α.val ≫ β.val, fun i ↦ weq.comp_mem _ _ (α.property i) (β.property i)⟩
  id_comp α := Subtype.ext (Category.id_comp α.val)
  comp_id α := Subtype.ext (Category.comp_id α.val)
  assoc α β γ := Subtype.ext (Category.assoc α.val β.val γ.val)

@[ext]
theorem hom_ext {F G : WeakFlag cof weq n} {α β : F ⟶ G} (h : α.val = β.val) : α = β :=
  Subtype.ext h

variable (cof' : MorphismProperty C) (hcof : cof ≤ cof')

/-- The actual inclusion of the smaller cofibration convention on finite flags. -/
def inclusion : WeakFlag cof weq n ⥤ WeakFlag cof' weq n where
  obj F := ⟨F.diagram, F.zero, fun f ↦ hcof _ (F.cofibration f)⟩
  map α := α

end WeakFlag

namespace FunctorialFactorization

variable {W : Structure C} (D : FunctorialFactorization W)
  [W.weq.HasTwoOutOfThreeProperty] (cof' : MorphismProperty C) (n : ℕ)

/-- The finite replacement functor lands in genuine cofibration flags and
acts on the actual pointwise weak-equivalence morphisms. -/
def flagReplacement : WeakFlag cof' W.weq n ⥤ WeakFlag W.cof W.weq n where
  obj F := {
    diagram := (finiteReplacement D n).obj F.diagram
    zero := by rw [finiteReplacement_obj_zero]; exact F.zero
    cofibration f := finiteReplacement_map_cof D n F.diagram f }
  map α := ⟨(finiteReplacement D n).map α.val,
    finiteReplacement_map_weak D n α.val α.property⟩
  map_id F := Subtype.ext ((finiteReplacement D n).map_id F.diagram)
  map_comp α β := Subtype.ext ((finiteReplacement D n).map_comp α.val β.val)

variable (hcof : W.cof ≤ cof')

/-- Replacing a smaller-cofibration flag admits a natural weak comparison
back to that same flag in the smaller-cofibration category. -/
def flagSourceComparison :
    WeakFlag.inclusion cof' hcof ⋙ flagReplacement D cof' n ⟶ 𝟭 (WeakFlag W.cof W.weq n) where
  app F := ⟨(finiteProjection D n).app F.diagram, finiteProjection_weak D n F.diagram⟩
  naturality _ _ α := Subtype.ext ((finiteProjection D n).naturality α.val)

/-- The analogous natural weak comparison in the enlarged-cofibration category. -/
def flagTargetComparison :
    flagReplacement D cof' n ⋙ WeakFlag.inclusion cof' hcof ⟶ 𝟭 (WeakFlag cof' W.weq n) where
  app F := ⟨(finiteProjection D n).app F.diagram, finiteProjection_weak D n F.diagram⟩
  naturality _ _ α := Subtype.ext ((finiteProjection D n).naturality α.val)

/-- Enlarging cofibrations induces an actual homotopy equivalence on the
classifying spaces of weak-equivalence finite flags. The forward map is
exactly the canonical inclusion; no equivalence hypothesis is supplied. -/
def flagInclusionClassifyingHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (WeakFlag W.cof W.weq n))
      (ClassifyingSpace (WeakFlag cof' W.weq n)) where
  toFun := (classifyingSpaceMap (WeakFlag.inclusion cof' hcof)).hom
  invFun := (classifyingSpaceMap (flagReplacement D cof' n)).hom
  left_inv := ⟨by
    simpa only [classifyingSpaceMap_id, classifyingSpaceMap_comp, TopCat.hom_id,
      TopCat.hom_comp] using
        classifyingSpaceNaturalTransformationHomotopy (flagSourceComparison D cof' n hcof)⟩
  right_inv := ⟨by
    simpa only [classifyingSpaceMap_id, classifyingSpaceMap_comp, TopCat.hom_id,
      TopCat.hom_comp] using
        classifyingSpaceNaturalTransformationHomotopy (flagTargetComparison D cof' n hcof)⟩

@[simp]
theorem flagInclusionClassifyingHomotopyEquiv_toFun :
    (flagInclusionClassifyingHomotopyEquiv D cof' n hcof).toFun =
      (classifyingSpaceMap (WeakFlag.inclusion cof' hcof)).hom := rfl

end FunctorialFactorization

end CategoryTheory.Waldhausen
