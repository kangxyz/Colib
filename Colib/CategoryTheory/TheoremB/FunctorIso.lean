/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Comma.Transitions
public import Colib.CategoryTheory.TheoremB.Conditions
public import Colib.CategoryTheory.TheoremA.Conclusion

/-!
# Natural-isomorphism transport of comma transition equivalences

Implementation source: `Quillen/CategoryTheory/TheoremB/FunctorIso.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual simplex families,
path coordinates, and endpoint data are retained under native ownership.
-/
@[expose] public section

noncomputable section
open Topology CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false
namespace CategoryTheory.TheoremB
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {F G : C ⥤ D} (e : F ≅ G)

/-- Natural-isomorphic functors have the same actual homotopy-equivalence
condition on all comma transitions. No transition equivalence is inferred
from mere connectedness of the commas. -/
theorem transitionHomotopyEquivalences_of_natIso (e : F ≅ G)
    (h : TransitionHomotopyEquivalences F) : TransitionHomotopyEquivalences G := by
  intro d d' f
  let s := equivalenceClassifyingHomotopyEquiv (CostructuredArrow.mapNatIso (T := d) e)
  let t := (transitionHomotopyEquiv F h f).trans
    (equivalenceClassifyingHomotopyEquiv (CostructuredArrow.mapNatIso (T := d') e))
  let E := TheoremA.homotopyEquivOfTriangle s t (transitionMap G f)
    (by
      have H := classifyingSpaceNaturalTransformationHomotopy (commaIsoTransitionIso e f).hom
      exact ⟨H.cast (by simp only [classifyingSpaceMap_comp, TopCat.hom_comp]; rfl)
        (by simp only [classifyingSpaceMap_comp, TopCat.hom_comp]; rfl)⟩)
  exact ⟨E.invFun, E.left_inv, E.right_inv⟩

end CategoryTheory.TheoremB
