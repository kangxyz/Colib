/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.KTheory.Waldhausen.Fibration.GeneralComparison
public import Colib.KTheory.Waldhausen.GilletWaldhausen.FibrationQuotient
public import Colib.CategoryTheory.Waldhausen.Fibration.ComplexExtension
public import Colib.CategoryTheory.Waldhausen.SplitComplexes.Approximation
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.ComplexSecondEndpoint

/-! # Gillet-Waldhausen with the original object and hom universes

The genuine bounded-complex cylinder and general-universe global fibration
give a K-equivalence on the original degree-zero single-insertion map in
every degree, including zero. The term property contains zero and is closed
under isomorphisms, extensions and kernels. The precise abelian ambient
category and all actual maps remain unchanged.


Implementation provenance:
`Quillen/Waldhausen/GilletWaldhausen/GeneralComparison.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps, bounds, hypotheses
and independent object/hom universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.Waldhausen.Fibration


open CategoryTheory.ExactCategory
open CochainComplex

noncomputable section
open Topology
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.Waldhausen.GilletWaldhausen
open Fibration
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type (max u v)} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]

/-- The unchanged bounded-complex canonical fiber map is weak in the original universes. -/
theorem boundedTerms_canonicalFiberMap_isWeakHomotopyEquivalence_general :
    IsWeakHomotopyEquivalence (canonicalFiberMap (boundedTermsNested P)) := by
  let : (boundedTermsNested P).coarse.weq.HasTwoOutOfThreeProperty :=
    complexSubcategory_saturated (boundedTerms P)
  exact canonicalFiberMap_isWeakHomotopyEquivalence_general (boundedTermsNested P)
    (complexSubcategory_extensionAxiom (boundedTerms P))
    (complexJointData (boundedTerms P) (boundedTerms_mappingCone P)
      (fun K hK ↦ boundedTerms_shift P hK 1))
    (complexJointData_secondEndpointSection (boundedTerms P) (boundedTerms_mappingCone P)
      (fun K hK ↦ boundedTerms_shift P hK 1))

variable [(abelianExactStructure A).IsKernelClosed P]
local instance generalAssembly_termPropertyProducts : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P

/-- The exact original coarse-single KMap is bijective in every degree, including zero. -/
theorem boundedTermsSingle_coarse_KMap_bijective_general (n : ℕ) :
    Function.Bijective (KMap (boundedTermsSingle_coarseExact P 0) n) :=
  boundedTermsSingle_coarse_KMap_bijective_of_canonicalFiber_weak P
    (boundedTerms_canonicalFiberMap_isWeakHomotopyEquivalence_general P) n

/-- The general-universe equivalence retains the original coarse-single forward map. -/
def boundedTermsSingleCoarseKEquivGeneral (n : ℕ) :
    (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K n ≃*
      (boundedTermsNested P).coarse.K n :=
  boundedTermsSingleCoarseKEquivOfCanonicalFiberWeakEquivalence P
    (boundedTerms_canonicalFiberMap_isWeakHomotopyEquivalence_general P) n

/-- The underlying monoid homomorphism of this K-equivalence. -/
@[simp] theorem boundedTermsSingleCoarseKEquivGeneral_coe (n : ℕ) :
    MonoidHomClass.toMonoidHom (boundedTermsSingleCoarseKEquivGeneral P n) =
      KMap (boundedTermsSingle_coarseExact P 0) n := rfl


end CategoryTheory.Waldhausen.GilletWaldhausen

namespace CategoryTheory.Waldhausen.GilletWaldhausen

attribute [colib_tag "COL-0260",
  colib_ref "WeibelKBook" "V, Theorem 2.2, pp. 13-14" "adaptation"
    "Connective K-group bijectivity for the original single-complex map, including K-zero; \
    inherited exact subcategory closed under kernels of surjections in the actual abelian ambient"]
  boundedTermsSingle_coarse_KMap_bijective_general
  boundedTermsSingleCoarseKEquivGeneral
  boundedTermsSingleCoarseKEquivGeneral_coe

attribute [colib_tag "COL-0260"]
  boundedTerms_canonicalFiberMap_isWeakHomotopyEquivalence_general

end CategoryTheory.Waldhausen.GilletWaldhausen
