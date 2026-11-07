/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Comma.Transitions
public import Colib.CategoryTheory.TheoremB.FunctorIso
public import Colib.CategoryTheory.TheoremB.StructuredComparison

/-!
# Natural-isomorphism transport of structured transitions

Implementation source: `Quillen/CategoryTheory/TheoremB/StructuredFunctorIso.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual simplex families,
path coordinates, and endpoint data are retained under native ownership.
-/
@[expose] public section

noncomputable section
universe u
open Topology CategoryTheory
set_option backward.isDefEq.respectTransparency false
namespace CategoryTheory.TheoremB
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {F G : C ⥤ D}

theorem structuredTransitionHomotopyEquivalences_of_natIso (e : F ≅ G)
    (h : StructuredTransitionHomotopyEquivalences F) :
    StructuredTransitionHomotopyEquivalences G := by
  intro d d' f
  let s := equivalenceClassifyingHomotopyEquiv (StructuredArrow.mapNatIso (S := d') e)
  let t := (structuredTransitionHomotopyEquiv F h f).trans
    (equivalenceClassifyingHomotopyEquiv (StructuredArrow.mapNatIso (S := d) e))
  let E := TheoremA.homotopyEquivOfTriangle s t (structuredTransitionMap G f)
    (by
      have H := classifyingSpaceNaturalTransformationHomotopy (structuredCommaIsoTransitionIso e
        f).hom
      exact ⟨H.cast (by simp only [classifyingSpaceMap_comp, TopCat.hom_comp]; rfl)
        (by simp only [classifyingSpaceMap_comp, TopCat.hom_comp]; rfl)⟩)
  exact ⟨E.invFun, E.left_inv, E.right_inv⟩

end CategoryTheory.TheoremB
