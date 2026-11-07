/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.AsSmall.Fiber
public import Colib.CategoryTheory.Waldhausen.AsSmall.Joint
public import Colib.KTheory.Waldhausen.Fibration.GlobalComparison

/-! # The original global fibration with distinct category universes

The exact common-universe model transports both structural cylinder data and
the actual canonical fiber comparison, including its full nullhomotopy path.
The result concerns the unchanged original map in its original universes.


Implementation provenance:
`Quillen/Waldhausen/Fibration/GeneralComparison.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.Waldhausen.Fibration
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) [N.coarse.weq.HasTwoOutOfThreeProperty]

/-- Structural cylinder data on the original common-universe model gives the
weak theorem for the original canonical fiber map, preserving its full path. -/
theorem canonicalFiberMap_isWeakHomotopyEquivalence_of_asSmallCylinder
    (he : ExtensionAxiom N.coarse) (D : RowFactorization.JointData N.asSmall)
    (hs : RowFactorization.SecondEndpointSection N.asSmall D) :
    IsWeakHomotopyEquivalence (canonicalFiberMap N) := by
  let : N.asSmall.coarse.weq.HasTwoOutOfThreeProperty :=
    N.coarse.asSmall_twoOutOfThree
  exact canonicalFiberMap_isWeakHomotopyEquivalence_of_asSmall N
    (canonicalFiberMap_isWeakHomotopyEquivalence N.asSmall
      (N.coarse.asSmall_extensionAxiom he) D hs)
/-- The original global fibration theorem for distinct object and hom universes. -/
theorem canonicalFiberMap_isWeakHomotopyEquivalence_general
    (he : ExtensionAxiom N.coarse) (D : RowFactorization.JointData N)
    (hs : RowFactorization.SecondEndpointSection N D) :
    IsWeakHomotopyEquivalence (canonicalFiberMap N) :=
  canonicalFiberMap_isWeakHomotopyEquivalence_of_asSmallCylinder N he D.asSmall hs.asSmall
end CategoryTheory.Waldhausen.Fibration


namespace CategoryTheory.Waldhausen.Fibration

attribute [colib_tag "COL-0254",
  colib_ref "Waldhausen1985" "Section 1.6, Theorem 1.6.4"
    "adaptation"
    "Original canonical fiber map in distinct universes, under coarse two-out-of-three, \
    extension, joint cylinder data and a second-endpoint section"]
  canonicalFiberMap_isWeakHomotopyEquivalence_general

end CategoryTheory.Waldhausen.Fibration
