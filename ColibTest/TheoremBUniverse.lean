/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.CategoryTheory.TheoremB.StructuredUniverseComparison
import Colib.CategoryTheory.TheoremB.UniverseWeakComparison

/-! # Original Theorem B maps with independent category universes -/

open CategoryTheory Topology
open scoped Topology
universe u₁ v₁ u₂ v₂ w

namespace CategoryTheory.TheoremB

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

example (h : StructuredTransitionWeakEquivalencesUniversal F) (d : D) :
    IsWeakHomotopyEquivalence (structuredFiberComparisonUniversal F d) :=
  structuredFiberComparisonUniversal_isWeakHomotopyEquivalence F h d

example (h : TransitionWeakEquivalencesUniversal F) (d : D)
    (hD : IsWeakHomotopyEquivalence (ContinuousMap.const (ClassifyingSpace D)
      (PUnit.unit : PUnit.{w + 1}))) :
    IsWeakHomotopyEquivalence (classifyingSpaceMapUniversal (CostructuredArrow.proj F d)) :=
  commaProjectionUniversal_isWeakHomotopyEquivalence_of_weakBase F h d hD

example (c : C) :
    structuredFiberComparisonUniversal F (F.obj c)
      (classifyingSpacePoint (StructuredArrow.mk (𝟙 (F.obj c)))) =
      HomotopyFiber.basepoint (classifyingSpaceMapUniversal F) (classifyingSpacePoint (F.obj c))
        (classifyingSpacePoint c) (classifyingSpaceMapUniversal_point F c) :=
  structuredFiberComparisonUniversal_identity F c

example (d : D) (X : StructuredArrow d F) (t : unitInterval) :
    (structuredFiberComparisonUniversal F d (classifyingSpacePoint X)).val.2 t =
      classifyingSpacePath X.hom (unitInterval.symm t) :=
  structuredFiberComparisonUniversal_vertex_path F d X t

end CategoryTheory.TheoremB
