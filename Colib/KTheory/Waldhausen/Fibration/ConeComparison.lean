/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Fibration.SpectrumComparison
public import Colib.KTheory.Waldhausen.Iterated.ConeFiberExcision
public import Colib.Topology.Prespectrum.ConeDescStableEquivalence

/-!
# The actual Waldhausen fibration cone comparison

The original zero-to-acyclic null track descends from the cone of the unchanged acyclic
inclusion to the unchanged coarse S-prespectrum. Genuine S-model excision and the proved
Waldhausen fiber theorem make this same map a stable equivalence. Its original signed
boundary, entire cylinder and target inclusion remain specified.
-/
/-! Implementation provenance: `Quillen/Waldhausen/Fibration/ConeComparison.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original maps, full null track, degree bounds, signed boundary and independent
object/hom universes are retained using the native strict chosen-zero subcategory. -/
@[expose] public section

open CategoryTheory.Waldhausen.IteratedS

noncomputable section
open CategoryTheory Topology.LoopPrespectrum
universe u v
namespace CategoryTheory.Waldhausen.Fibration
open Topology SmallWaldhausenCategory
open IteratedS
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)

/-- The original entire acyclic null track gives the unchanged coarse-spectrum cone map. -/
def canonicalConePrespectrumMap :
    mappingCone (acyclicInclusionPrespectrumMap N) ⟶ originalPrespectrum N.coarse :=
  mappingConeDesc (acyclicInclusionPrespectrumMap N) (changeWeakPrespectrumMap N)
    (acyclicPrespectrumNullhomotopy N)

/-- The cone target face is precisely the original change-of-weak-equivalences map. -/
theorem canonicalConePrespectrumMap_inclusion :
    mappingConeInclusion (acyclicInclusionPrespectrumMap N) ≫ canonicalConePrespectrumMap N =
      changeWeakPrespectrumMap N :=
  mappingConeInclusion_desc _ _ _

/-- Every point of the cylinder retains the actual original acyclic nullhomotopy time. -/
theorem canonicalConePrespectrumMap_cylinder (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (acyclicStructure N)).space n) :
    (canonicalConePrespectrumMap N).map n
        (ReducedMappingCone.cylinder ((originalPrespectrum (acyclicStructure N)).point n)
          ((originalPrespectrum V).point n) ((acyclicInclusionPrespectrumMap N).map n) (s, x)) =
      (acyclicPrespectrumNullhomotopy N).level n (s, x) := rfl

/-- The original signed boundary retains the canonical fiber comparison and its full null track. -/
theorem canonicalConePrespectrumMap_connecting (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map (canonicalConePrespectrumMap N) ≫
        stableFiberConnecting (changeWeakPrespectrumMap N) d =
      stableMappingConeConnecting (acyclicInclusionPrespectrumMap N)
          (originalPrespectrum_mappingConeFiberComparison_isStableEquivalence _ _ _) d ≫
        (stableHomotopyFunctor d).map (canonicalFiberPrespectrumMap N) :=
  mappingConeDesc_connecting _ _ _ _ d

/-- The actual proved original fiber comparison gives stability of the same original cone map. -/
theorem canonicalConePrespectrumMap_isStableEquivalence_of_weak
    (h : IsWeakHomotopyEquivalence (canonicalFiberMap N)) :
    IsStableEquivalence (canonicalConePrespectrumMap N) :=
  mappingConeDesc_isStableEquivalence _ _ _
    (originalPrespectrum_mappingConeFiberComparison_isStableEquivalence _ _ _)
    (canonicalFiberPrespectrumMap_isStableEquivalence_of_weak N h)

/-- Structural Waldhausen fibration hypotheses discharge the cone comparison completely. -/
theorem canonicalConePrespectrumMap_isStableEquivalence_general
    [N.coarse.weq.HasTwoOutOfThreeProperty]
    (he : ExtensionAxiom N.coarse) (D : RowFactorization.JointData N)
    (hs : RowFactorization.SecondEndpointSection N D) :
    IsStableEquivalence (canonicalConePrespectrumMap N) :=
  canonicalConePrespectrumMap_isStableEquivalence_of_weak N
    (canonicalFiberMap_isWeakHomotopyEquivalence_general N he D hs)

end CategoryTheory.Waldhausen.Fibration

attribute [colib_tag "COL-0288",
  colib_ref "Waldhausen1985" "Section 1.6, Theorem 1.6.4 and proof, pp. 350-352" "ingredient"
    "The original fiber theorem is combined with proved stable S-model cone excision",
  colib_ref "ThomasonTrobaugh1990" "Sections 1.8.1-1.8.2, p. 263" "ingredient"
    "The spectrum fiber sequence and chosen zero nullhomotopy precede actual cone descent"]
  CategoryTheory.Waldhausen.Fibration.canonicalConePrespectrumMap_isStableEquivalence_general

attribute [colib_tag "COL-0288"]
  CategoryTheory.Waldhausen.Fibration.canonicalConePrespectrumMap_inclusion
  CategoryTheory.Waldhausen.Fibration.canonicalConePrespectrumMap_cylinder
  CategoryTheory.Waldhausen.Fibration.canonicalConePrespectrumMap_connecting
