/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.ComplexSubcategory

public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.TruncationTransformations
public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Pullbacks
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.QuotientExact
public import Colib.CategoryTheory.Waldhausen.GilletWaldhausen.ExactFunctorSequence

/-!
# The genuine acyclic truncation cofibration sequence

The actual truncation inclusion, identity functor, and actual cokernel
projection satisfy all structural hypotheses of the additivity theorem.
The relative-pushout cofibration condition is derived from exactness of
the quotient, rather than supplied as a hypothesis.


Implementation provenance:
`Quillen/Waldhausen/GilletWaldhausen/TruncationCofibrationSequence.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps, bounds, hypotheses
and independent object/hom universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.ExactCategory
open CochainComplex



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe v u

namespace CategoryTheory.Waldhausen.GilletWaldhausen

attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsKernelClosed P]

variable [(abelianExactStructure A).IsExtensionClosed P]

/-- The actual truncation sequence satisfies the ordinary relative-cofibration
condition for the inherited exact structure. -/
theorem boundedAcyclicTruncation_cofibration (n : ℤ) :
    Additivity.IsCofibrationTransformation (ofExactCategory (boundedAcyclicExactStructure P))
      (boundedAcyclicTruncationInclusion P n)
      (ofExactCategory (boundedAcyclicExactStructure P)) :=
  exactFunctorSequence_cofibration _ _ _ _ (boundedAcyclicTruncation_comp_zero P n)
    (acyclicTruncationSequenceFunctor_conflation P n)
    (boundedAcyclicQuotientExactFunctor P n).map_inflation

/-- A genuine cofibration sequence of exact functors, with isomorphism weak
 equivalences and the original actual truncation/cokernel maps. -/
theorem boundedAcyclicTruncation_isCofibrationSequence (n : ℤ) :
    Additivity.IsCofibrationSequence (ofExactCategory (boundedAcyclicExactStructure P))
      (ofExactCategory (boundedAcyclicExactStructure P))
      (boundedAcyclicTruncationInclusion P n) (boundedAcyclicTruncationProjection P n) :=
  exactFunctorSequence_isCofibrationSequence _ _ _ _ (boundedAcyclicTruncation_comp_zero P n)
    (acyclicTruncationSequenceFunctor_conflation P n)
    (boundedAcyclicTruncLEExactFunctor P n) (CategoryTheory.ExactCategory.ExactFunctor.id
      (boundedAcyclicExactStructure P))
    (boundedAcyclicQuotientExactFunctor P n) rfl rfl rfl

omit [(abelianExactStructure A).IsKernelClosed P] in
/-- Exactness also holds with genuine quasi-isomorphisms, since these are
all actual maps in the bounded acyclic category. -/
theorem boundedAcyclicExactFunctor_waldhausenExact
    (F : ExactCategory.ExactFunctor (boundedAcyclicExactStructure P)
      (boundedAcyclicExactStructure P)) :
    IsExact (complexSubcategory (boundedAcyclic P)).cof
      (complexSubcategory (boundedAcyclic P)).weq
      (complexSubcategory (boundedAcyclic P)).cof
      (complexSubcategory (boundedAcyclic P)).weq F.toFunctor where
  zero hZ := F.toFunctor.map_isZero hZ
  cofibration f hf := F.map_inflation f hf
  weak f _ := boundedAcyclic_map_quasiIso P (F.toFunctor.map f)
  pushout hi h := F.map_isPushout hi h

/-- The same actual truncation cofibration sequence for genuine quasi-isomorphisms. -/
theorem boundedAcyclicTruncation_isCofibrationSequence_quasiIso (n : ℤ) :
    Additivity.IsCofibrationSequence (complexSubcategory (boundedAcyclic P))
      (complexSubcategory (boundedAcyclic P))
      (boundedAcyclicTruncationInclusion P n) (boundedAcyclicTruncationProjection P n) where
  exactF := boundedAcyclicExactFunctor_waldhausenExact P (boundedAcyclicTruncLEExactFunctor P n)
  exactG := IsExact.id _ _
  exactH := boundedAcyclicExactFunctor_waldhausenExact P (boundedAcyclicQuotientExactFunctor P n)
  cofibration := {
    app_cof := (boundedAcyclicTruncation_cofibration P n).app_cof
    relative_cof f hf := (boundedAcyclicTruncation_cofibration P n).relative_cof f hf }
  cofiber := (boundedAcyclicTruncation_isCofibrationSequence P n).cofiber

end CategoryTheory.Waldhausen.GilletWaldhausen
