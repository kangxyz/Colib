/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.ConeStableExactness
public import Colib.Topology.Prespectrum.FiberSquareDetection

/-!
# The original cone descent of a genuine fiber comparison

The original target map and specified entire null track give the usual cone descent. Its
strict square on the cone inclusion carries the literal cone-cylinder fiber lift to the
specified original fiber lift. Actual stable excision and stability of that fiber lift then
prove stability of the unchanged cone descent. Conversely, excision and stable cone descent
give stability of the specified original fiber lift. These premises remain explicit here;
concrete Waldhausen applications discharge them from proved excision and the fibration theorem.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/ConeDescStableEquivalence.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The actual cone, full independent cylinder and loop parameters, signed degrees and
original hypotheses are retained under their native mathematical owners. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum
variable {E F G : LoopPrespectrum.{u}} (f : E ⟶ F) (g : F ⟶ G)
    (H : Homotopy (f ≫ g) (zeroHom E G))

/-- The original cone descent gives a strict square over the identity of the original target. -/
def mappingConeDescSquare : Arrow.mk (mappingConeInclusion f) ⟶ Arrow.mk g :=
  Arrow.homMk (𝟙 F) (mappingConeDesc f g H)
    ((Category.id_comp g).trans (mappingConeInclusion_desc f g H).symm)

/-- The entire original null track is exactly the image of the cone-cylinder fiber path. -/
theorem mappingConeDescSquare_fiberComparison :
    mappingConeFiberComparison f ≫ homotopyFiberMap (mappingConeDescSquare f g H) =
      homotopyFiberLift g f H := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  rfl

/-- The original signed cone boundary is carried to the original fiber boundary by this lift. -/
theorem mappingConeDesc_connecting
    (he : IsStableEquivalence (mappingConeFiberComparison f)) (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map (mappingConeDesc f g H) ≫
        stableFiberConnecting g d =
      stableMappingConeConnecting f he d ≫
        (stableHomotopyFunctor d).map (homotopyFiberLift g f H) := by
  have hn := stableFiberConnecting_naturality (mappingConeDescSquare f g H) d
  change (stableHomotopyFunctor (d + 1)).map (mappingConeDesc f g H) ≫
    stableFiberConnecting g d = stableFiberConnecting (mappingConeInclusion f) d ≫
      (stableHomotopyFunctor d).map (homotopyFiberMap (mappingConeDescSquare f g H)) at hn
  rw [← stableMappingConeConnecting_comparison f he d, Category.assoc,
    ← Functor.map_comp, mappingConeDescSquare_fiberComparison] at hn
  exact hn

/-- Genuine original excision and the specified stable fiber lift imply stable cone descent. -/
theorem mappingConeDesc_isStableEquivalence
    (he : IsStableEquivalence (mappingConeFiberComparison f))
    (hf : IsStableEquivalence (homotopyFiberLift g f H)) :
    IsStableEquivalence (mappingConeDesc f g H) := by
  apply right_isStableEquivalence_of_fiber (mappingConeDescSquare f g H)
    (IsStableEquivalence.id F)
  intro d
  let := he d
  apply (isIso_comp_left_iff
    ((stableHomotopyFunctor d).map (mappingConeFiberComparison f)) _).mp
  rw [← Functor.map_comp, mappingConeDescSquare_fiberComparison]
  exact hf d

/-- Genuine original excision and stable cone descent make the same whole-null fiber lift stable. -/
theorem homotopyFiberLift_isStableEquivalence_of_coneDesc
    (he : IsStableEquivalence (mappingConeFiberComparison f))
    (hd : IsStableEquivalence (mappingConeDesc f g H)) :
    IsStableEquivalence (homotopyFiberLift g f H) := by
  rw [← mappingConeDescSquare_fiberComparison]
  exact he.comp (homotopyFiberMap_isStableEquivalence
    (mappingConeDescSquare f g H) (IsStableEquivalence.id F) hd)

end Topology.LoopPrespectrum
