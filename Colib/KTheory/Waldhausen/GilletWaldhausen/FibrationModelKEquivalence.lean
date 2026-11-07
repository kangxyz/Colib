/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.Waldhausen.GilletWaldhausen.FibrationModels
public import Colib.KTheory.Waldhausen.ExactEquivalence

/-! # The original bounded-acyclic model identification on K-theory

This changes only two presentations of the same actual fine acyclic category.
It does not identify that category with the homotopy fiber of a change of weak
classes. The latter fibration theorem is a separate obligation.


Implementation provenance:
`Quillen/Waldhausen/GilletWaldhausen/FibrationModelKEquivalence.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps, bounds, hypotheses
and independent object/hom universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.ExactCategory
open CochainComplex


noncomputable section
open Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]

/-- The actual identity-on-complexes exact equivalence, on the original K-groups. -/
def boundedAcyclicFiberKEquiv (n : ℕ) :
    (ofExactCategory (boundedAcyclicExactStructure P)).K n ≃*
      (Fibration.acyclicStructure (boundedTermsNested P)).K n :=
  KEquivOfExactEquivalence (boundedAcyclicFiberEquivalence P)
    (boundedAcyclicToFiberObjects_exact P) (fiberObjectsToBoundedAcyclic_exact P) n

/-- The forward map is exactly the original identity-on-complexes K-map. -/
@[simp] theorem boundedAcyclicFiberKEquiv_coe (n : ℕ) :
    (↑(boundedAcyclicFiberKEquiv P n) : (ofExactCategory (boundedAcyclicExactStructure P)).K n
        →* (Fibration.acyclicStructure (boundedTermsNested P)).K n) = KMap
        (boundedAcyclicToFiberObjects_exact P) n := rfl


/-- The inverse is exactly the original inverse-presentation K-map. -/
@[simp] theorem boundedAcyclicFiberKEquiv_symm_coe (n : ℕ) :
    (↑(boundedAcyclicFiberKEquiv P n).symm : (Fibration.acyclicStructure (boundedTermsNested
        P)).K n →* (ofExactCategory (boundedAcyclicExactStructure P)).K n) = KMap
        (fiberObjectsToBoundedAcyclic_exact P) n := rfl


/-- After the actual fiber-object inclusion, the original bounded-acyclic
inclusion K-map is recovered exactly. -/
theorem boundedAcyclicFiberKEquiv_inclusion (n : ℕ) :
    (KMap (Fibration.acyclicInclusion_exact (boundedTermsNested P)) n).comp
      (boundedAcyclicFiberKEquiv P n).toMonoidHom =
        KMap (boundedAcyclicTermsExactInclusion P).waldhausenExact n := by
  simp only [MulEquiv.toMonoidHom_eq_coe]
  rw [boundedAcyclicFiberKEquiv_coe, KMap_comp_KMap]

end CategoryTheory.Waldhausen.GilletWaldhausen
