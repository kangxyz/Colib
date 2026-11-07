/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.GrothendieckTelescope
public import Colib.Topology.LocalCoefficients.HomotopyInvariance

/-!
Adapted from `Quillen/Topology/LocalCoefficients/TelescopeTransitions.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining original transition maps.


# Original stage transitions with actual local-coefficient transport

Fiber inclusions into the infinite Grothendieck model commute with the original
sequence transitions by their specified natural-transformation homotopies.
These tracks give the necessary coefficient conversion. The resulting genuine
stage homology map commutes with the original map to infinite-model homology.
-/

@[expose] public section

open FundamentalGroupoid.LocalCoefficients


open CategoryTheory
noncomputable section
universe u

namespace CategoryTheory.Grothendieck.Telescope

open FundamentalGroupoid.LocalCoefficients

variable (F : ℕ ⥤ Cat.{u, u})

/-- The actual track transport identifying the two stage coefficient systems. -/
def stagePullbackIso {n m : ℕ} (h : n ≤ m)
    (A : System.{u, u} (ClassifyingSpace (Model F))) :
    pullback (classifyingSpaceMap (Grothendieck.ι F n)).hom A ≅
      pullback (classifyingSpaceMap (F.map (homOfLE h)).toFunctor).hom
        (pullback (classifyingSpaceMap (Grothendieck.ι F m)).hom A) :=
  homotopyPullbackIso (stageTransitionClassifyingHomotopy F h) A ≪≫
    pullbackCompositionIso (classifyingSpaceMap (F.map (homOfLE h)).toFunctor).hom
      (classifyingSpaceMap (Grothendieck.ι F m)).hom A

/-- At a point, the coefficient conversion is exactly the stabilization track. -/
theorem stagePullbackIso_hom_app {n m : ℕ} (h : n ≤ m)
    (A : System.{u, u} (ClassifyingSpace (Model F))) (x : ClassifyingSpace (F.obj n)) :
    (stagePullbackIso F h A).hom.app (FundamentalGroupoid.mk x) =
      FundamentalGroupoid.LocalCoefficients.transport A
        ((stageTransitionClassifyingHomotopy F h).evalAt x) := by
  change FundamentalGroupoid.LocalCoefficients.transport A
    ((stageTransitionClassifyingHomotopy F h).evalAt x) ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The original sequence map on homology after its specified coefficient transport. -/
def stageHomologyTransition {n m : ℕ} (h : n ≤ m)
    (A : System.{u, u} (ClassifyingSpace (Model F))) (k : ℕ) :
    homology (pullback (classifyingSpaceMap (Grothendieck.ι F n)).hom A) k ⟶
      homology (pullback (classifyingSpaceMap (Grothendieck.ι F m)).hom A) k :=
  coefficientHomologyMap (stagePullbackIso F h A).hom k ≫
    pushforwardHomologyMap (classifyingSpaceMap (F.map (homOfLE h)).toFunctor).hom
      (pullback (classifyingSpaceMap (Grothendieck.ι F m)).hom A) k

/-- The transported original transition commutes with the original infinite-model map. -/
@[reassoc]
theorem stageHomologyTransition_to_infinite {n m : ℕ} (h : n ≤ m)
    (A : System.{u, u} (ClassifyingSpace (Model F))) (k : ℕ) :
    stageHomologyTransition F h A k ≫
        pushforwardHomologyMap (classifyingSpaceMap (Grothendieck.ι F m)).hom A k =
      pushforwardHomologyMap (classifyingSpaceMap (Grothendieck.ι F n)).hom A k := by
  rw [pushforwardHomologyMap_homotopy (stageTransitionClassifyingHomotopy F h) A k,
    pushforwardHomologyMap_comp]
  change (coefficientHomologyMap
      ((homotopyPullbackIso (stageTransitionClassifyingHomotopy F h) A).hom ≫
        (pullbackCompositionIso _ _ A).hom) k ≫ _) ≫ _ = _
  rw [coefficientHomologyMap_comp]
  simp only [Category.assoc]
  rfl

end CategoryTheory.Grothendieck.Telescope
