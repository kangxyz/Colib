/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.ClassifyingSpace.InverseHomotopy
public import Colib.Topology.HomotopyFiber.Nullhomotopy
public import Colib.CategoryTheory.TheoremB.Naturality

/-!
# Natural-isomorphism nullhomotopies and actual fiber lifts

Implementation source: `Quillen/CategoryTheory/TheoremB/StructuredIsoHomotopy.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual simplex families,
path coordinates, and endpoint data are retained under native ownership.
-/
@[expose] public section
noncomputable section
open Topology CategoryTheory SSet Opposite MonoidalCategory CartesianMonoidalCategory Convexity
open scoped Simplicial Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.TheoremB
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
/-- A natural isomorphism to a constant functor gives the direct nullhomotopy. -/
def naturalIsoNullhomotopy {A : Type u} [SmallCategory A]
    (P : A ⥤ C) (F : C ⥤ D) (d : D) (e : P ⋙ F ≅ (Functor.const A).obj d) :
    ((classifyingSpaceMap F).hom.comp (classifyingSpaceMap P).hom).Homotopy
      (ContinuousMap.const _ (classifyingSpacePoint d)) :=
  (classifyingSpaceNaturalTransformationHomotopy e.hom).cast
    (by simp only [classifyingSpaceMap_comp, TopCat.hom_comp])
    (by rw [classifyingSpaceMap_const_direct]; rfl)

/-- The inverse natural isomorphism gives a second, reversed nullhomotopy. -/
def naturalIsoInverseNullhomotopy {A : Type u} [SmallCategory A]
    (P : A ⥤ C) (F : C ⥤ D) (d : D) (e : P ⋙ F ≅ (Functor.const A).obj d) :
    ((classifyingSpaceMap F).hom.comp (classifyingSpaceMap P).hom).Homotopy
      (ContinuousMap.const _ (classifyingSpacePoint d)) :=
  (classifyingSpaceNaturalTransformationHomotopy e.inv).symm.cast
    (by simp only [classifyingSpaceMap_comp, TopCat.hom_comp])
    (by rw [classifyingSpaceMap_const_direct]; rfl)

/-- Forward and reversed-inverse natural isomorphisms define canonically
homotopic actual fiber maps. This comparison fixes the source coordinate. -/
def naturalIsoFiberLiftHomotopy {A : Type u} [SmallCategory A]
    (P : A ⥤ C) (F : C ⥤ D) (d : D) (e : P ⋙ F ≅ (Functor.const A).obj d) :
    (HomotopyFiber.lift (classifyingSpaceMap F).hom (classifyingSpacePoint d)
      (classifyingSpaceMap P).hom (naturalIsoNullhomotopy P F d e)).Homotopy
    (HomotopyFiber.lift (classifyingSpaceMap F).hom (classifyingSpacePoint d)
      (classifyingSpaceMap P).hom (naturalIsoInverseNullhomotopy P F d e)) :=
  HomotopyFiber.fiberLiftNullhomotopyHomotopy _ _ _ _ _ (naturalIsoInverseHomotopy e.symm)
@[simp] theorem naturalIsoFiberLiftHomotopy_projection {A : Type u} [SmallCategory A]
    (P : A ⥤ C) (F : C ⥤ D) (d : D) (e : P ⋙ F ≅ (Functor.const A).obj d)
    (s : unitInterval) (x : ClassifyingSpace A) :
    (naturalIsoFiberLiftHomotopy P F d e (s, x)).1.1 = classifyingSpaceMap P x := rfl

end CategoryTheory.TheoremB
