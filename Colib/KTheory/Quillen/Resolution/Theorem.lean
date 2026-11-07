/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.KTheory.Quillen.Resolution.UnionSequential

/-!
# Quillen's finite-resolution theorem

A full inherited exact subcategory, closed under extensions and kernels of
admissible epimorphisms, has the same Quillen K-theory whenever every ambient
object has an actual finite admissible resolution by its objects. Lengths may
be unbounded over the category. The forward maps below are exactly the original
Q-inclusion and the canonically zero-normalized inclusion K-map.

The proof constructs the length-one comma contractions, proves resolving
closure of every finite-length stratum, and identifies the ambient Q-nerve
with their genuine filtered colimit. No homotopy equivalence or comma
contractibility is part of the input.

The original finite-resolution reference is Quillen, Section 4, Corollary 1.
Theorem 3 in that section is the length-one step, not by itself the statement
with arbitrary objectwise finite resolution lengths.
-/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.ExactCategory.Resolution
variable {C : Type u} [SmallCategory C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (P : ObjectProperty C)
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [E.IsExtensionClosed P]
  [E.IsKernelClosed P] [P.IsClosedUnderFiniteProducts]

/-- Quillen resolution with objectwise finite lengths, as a genuine
classifying-space homotopy equivalence. -/
def classifyingHomotopyEquiv (h : E.ResolutionHypothesis P) :
    ContinuousMap.HomotopyEquiv (ExactSubcategory.exactStructure E P).KSpace E.KSpace := by
  letI : Fact (E.ResolutionHypothesis P) := ⟨h⟩
  letI := inclusionOfLE_mapQ_isEquivalence_of_reverse E P (E.ResolutionLength P 0)
    (E.le_resolutionLength P 0) (fun X hX => (E.resolutionLength_zero_iff P X).1 hX)
  exact (classifyingHomotopyEquivOfIsEquivalence (intoStratumExact E P 0).mapQ).trans
    (stratumZeroToAmbientHomotopyEquiv E P)

/-- The theorem retains precisely the actual realized Q-inclusion. -/
@[simp] theorem classifyingHomotopyEquiv_toFun (h : E.ResolutionHypothesis P) :
    (classifyingHomotopyEquiv E P h).toFun =
      (classifyingSpaceMap (exactInclusion E P).mapQ).hom := by
  let : Fact (E.ResolutionHypothesis P) := ⟨h⟩
  change (stratumZeroToAmbientHomotopyEquiv E P).toFun.comp
    (classifyingSpaceMap (intoStratumExact E P 0).mapQ).hom = _
  rw [stratumZeroToAmbientHomotopyEquiv_toFun, ← TopCat.hom_comp,
    ← classifyingSpaceMap_comp, ← CategoryTheory.ExactCategory.ExactFunctor.mapQ_comp,
      exactInclusionOfLE_comp]

/-- Canonical zero normalization, along its actual natural isomorphism. -/
def normalizedClassifyingHomotopyEquiv (h : E.ResolutionHypothesis P) :
    ContinuousMap.HomotopyEquiv (ExactSubcategory.exactStructure E P).KSpace E.KSpace :=
  TheoremA.homotopyEquivWithMap (classifyingHomotopyEquiv E P h)
    (classifyingSpaceMap (exactInclusion E P).normalizedQ).hom (by
      rw [classifyingHomotopyEquiv_toFun]
      exact ⟨classifyingSpaceNaturalTransformationHomotopy
        (rebaseFunctorIso (exactInclusion E P).mapQ
          (QConstruction.of _ _ (0 : P.FullSubcategory)) (QConstruction.of _ _ (0 : C))
          (E.qIsoOfIso (exactInclusion E P).toFunctor.mapZeroObject)).inv⟩)

/-- The canonical inclusion-induced map is bijective in every nonnegative
Quillen K-degree, with no uniform resolution-length hypothesis. -/
theorem inclusionKMap_bijective (h : E.ResolutionHypothesis P) (n : ℕ) :
    Function.Bijective (inclusionKMap E P n) :=
  (exactInclusion E P).KMap_bijective_of_homotopyEquiv
    (normalizedClassifyingHomotopyEquiv E P h) rfl n

/-- The genuine Quillen resolution equivalence. -/
def KEquiv (h : E.ResolutionHypothesis P) (n : ℕ) :
    (ExactSubcategory.exactStructure E P).K n ≃* E.K n :=
  MulEquiv.ofBijective (inclusionKMap E P n) (inclusionKMap_bijective E P h n)

/-- The forward homomorphism is the original canonical inclusion map. -/
@[simp] theorem KEquiv_coe (h : E.ResolutionHypothesis P) (n : ℕ) :
    (↑(KEquiv E P h n) : (ExactSubcategory.exactStructure E P).K n →* E.K n) = inclusionKMap E P
        n := rfl

end CategoryTheory.ExactCategory.Resolution

attribute [colib_tag "COL-0237",
  colib_ref "WeibelKBook" "V, Resolution Theorem 3.1, page 20" "adaptation"
    "Objectwise-finite Quillen Resolution"]
  CategoryTheory.ExactCategory.Resolution.classifyingHomotopyEquiv
  CategoryTheory.ExactCategory.Resolution.inclusionKMap_bijective
  CategoryTheory.ExactCategory.Resolution.KEquiv
  CategoryTheory.ExactCategory.Resolution.KEquiv_coe

attribute [colib_ref "Quillen1973"
    "Section 4, Corollary 1 and proof, pp. 109-110" "adaptation"
    "Objectwise finite admissible resolutions, without a uniform length bound; extension and \
      kernel closure retained"]
  CategoryTheory.ExactCategory.Resolution.classifyingHomotopyEquiv
  CategoryTheory.ExactCategory.Resolution.inclusionKMap_bijective
  CategoryTheory.ExactCategory.Resolution.KEquiv
