/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.CategoryTheory.ExactCategory.Resolution.Strata
public import Colib.CategoryTheory.ExactCategory.Resolution.SubcategoryComparison
/-!
# Exact inclusions of finite-resolution-length strata

Under the original global finite-resolution and resolving-closure hypotheses,
the inherited strata have their actual exact inclusions. Every next-stratum
object has the original length-one resolution by the preceding stratum.
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

section Strata
variable [Fact (E.ResolutionHypothesis P)]

/-- The inherited exact category of objects with resolutions of length at
most `n`. Its exact axioms come from the proved extension closure. -/
abbrev stratumExactStructure (n : ℕ) : ExactStructure (E.ResolutionLength P n).FullSubcategory :=
  ExactSubcategory.exactStructure E (E.ResolutionLength P n)

/-- The canonical exact inclusion of adjacent length strata. -/
abbrev stratumExactInclusion (n : ℕ) :
    ExactFunctor (stratumExactStructure E P n) (stratumExactStructure E P (n + 1)) :=
  exactInclusionOfLE E (E.ResolutionLength P n) (E.ResolutionLength P (n + 1))
    (E.resolutionLength_mono P (Nat.le_succ n))

omit [P.IsClosedUnderFiniteProducts] in
/-- An object in the next stratum has a length-one admissible resolution
inside that stratum by objects in the preceding stratum. -/
theorem adjacentStratum_resolutionLength_one (n : ℕ)
    (X : (E.ResolutionLength P (n + 1)).FullSubcategory) :
    (stratumExactStructure E P (n + 1)).ResolutionLength
      ((E.ResolutionLength P n).inverseImage (E.ResolutionLength P (n + 1)).ι) 1 X := by
  obtain ⟨T⟩ := (E.resolutionLength_succ_iff P n X.obj).1 X.property
  let A : (E.ResolutionLength P (n + 1)).FullSubcategory :=
    ⟨T.syzygy, E.resolutionLength_mono P (Nat.le_succ n) _ T.syzygy_mem⟩
  let B : (E.ResolutionLength P (n + 1)).FullSubcategory :=
    ⟨T.middle, E.le_resolutionLength P (n + 1) _ T.middle_mem⟩
  let S : ShortComplex (E.ResolutionLength P (n + 1)).FullSubcategory :=
    ShortComplex.mk
      (ObjectProperty.homMk T.f : A ⟶ B)
      (ObjectProperty.homMk T.g : B ⟶ X)
      ((E.ResolutionLength P (n + 1)).hom_ext T.zero)
  have hS : (stratumExactStructure E P (n + 1)).conflation S := T.conflation
  exact ⟨.step S hS (E.le_resolutionLength P n _ T.middle_mem) (.of_mem T.syzygy_mem),
    Nat.le_refl 1⟩

/-- The canonical exact inclusion of any two ordered length strata. -/
abbrev stratumTransition {m n : ℕ} (h : m ≤ n) :
    ExactFunctor (stratumExactStructure E P m) (stratumExactStructure E P n) :=
  exactInclusionOfLE E (E.ResolutionLength P m) (E.ResolutionLength P n)
    (E.resolutionLength_mono P h)

/-- The original resolving category includes canonically in every stratum. -/
abbrev intoStratumExact (n : ℕ) :
    ExactFunctor (ExactSubcategory.exactStructure E P) (stratumExactStructure E P n) :=
  exactInclusionOfLE E P (E.ResolutionLength P n) (E.le_resolutionLength P n)

end Strata
end CategoryTheory.ExactCategory.Resolution

attribute [colib_tag "COL-0234",
  colib_ref "WeibelKBook" "V, 3.1 and Exercise 3.1" "adaptation"
    "Finite admissible resolutions and strata"]
  CategoryTheory.ExactCategory.Resolution.adjacentStratum_resolutionLength_one
