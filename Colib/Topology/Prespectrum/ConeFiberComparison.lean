/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.MappingCone
public import Colib.Topology.Prespectrum.FiberNaturality

/-!
# The original source-to-fiber comparison for a mapping cone

The actual cone cylinder constructs a strict map from the original source to the path-space fiber
of the original cone inclusion. Its projection is the original arrow, its entire fiber path is the
original cylinder, and strict arrow squares preserve both coordinates. No excision or stable
weak-equivalence assertion is made about this comparison.
-/

/-! Implementation provenance: `Quillen/Topology/Prespectrum/ConeFiberComparison.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The actual cone, full independent cylinder and loop parameters, signed degrees and
original hypotheses are retained under their native mathematical owners. -/
@[expose] public section

noncomputable section

open CategoryTheory
open scoped Topology unitInterval

universe u

namespace Topology.LoopPrespectrum

variable {E F : LoopPrespectrum.{u}} (f : E ⟶ F)

/-- The cone's original coherent nullhomotopy supplies the actual source-to-fiber comparison. -/
def mappingConeFiberComparison : E ⟶ homotopyFiber (mappingConeInclusion f) :=
  homotopyFiberLift (mappingConeInclusion f) f (mappingConeHomotopy f)

/-- The original arrow is unchanged after projection from the actual fiber. -/
@[simp]
theorem mappingConeFiberComparison_projection :
    mappingConeFiberComparison f ≫ homotopyFiberProjection (mappingConeInclusion f) = f :=
  homotopyFiberLift_projection _ _ _

/-- The source coordinate is the original map, without a homotopy replacement. -/
@[simp]
theorem mappingConeFiberComparison_source (n : ℕ) (x : E.space n) :
    ((mappingConeFiberComparison f).map n x).1.1 = f.map n x := rfl

/-- Every point of the original cone cylinder remains the actual fiber path. -/
@[simp]
theorem mappingConeFiberComparison_path (n : ℕ) (x : E.space n) (s : unitInterval) :
    ((mappingConeFiberComparison f).map n x).1.2 s =
      ReducedMappingCone.cylinder (E.point n) (F.point n) (f.map n) (s, x) := rfl

variable {A B : Arrow LoopPrespectrum.{u}}

/-- A strict arrow square gives the corresponding strict square of original cone inclusions. -/
def mappingConeInclusionSquare (sq : A ⟶ B) :
    Arrow.mk (mappingConeInclusion A.hom) ⟶ Arrow.mk (mappingConeInclusion B.hom) :=
  Arrow.homMk sq.right (mappingConeMap sq) (by
    apply Hom.ext
    funext n
    ext y
    rfl)

/-- The actual source-to-fiber comparison is natural, retaining the complete original cylinder. -/
theorem mappingConeFiberComparison_naturality (sq : A ⟶ B) :
    sq.left ≫ mappingConeFiberComparison B.hom =
      mappingConeFiberComparison A.hom ≫ homotopyFiberMap (mappingConeInclusionSquare sq) := by
  apply Hom.ext
  funext n
  ext x
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun h ↦ h.map n x) sq.w
  · rfl

end Topology.LoopPrespectrum
