/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.KTheory.GrothendieckGroup.Abelian
public import Colib.KTheory.GrothendieckGroup.Field

/-!
# Dimension for the standard exact structure on finite-dimensional vector spaces

This is the normalization of the algebraic conflation presentation through the
canonical comparison to the pinned Stacks Core Grothendieck group. It is not a
computation of a homotopy group of the Q-construction.
-/

@[expose] public noncomputable section

universe u

namespace CategoryTheory.ExactCategory

variable (k : Type u) [Field k]

attribute [local instance] Abelian.hasFiniteBiproducts

/-- Dimension identifies the conflation Grothendieck group for the standard exact
structure on finite-dimensional vector spaces with the integers. -/
def fgModuleExactRankEquiv :
    (abelianExactStructure (FGModuleCat.{u} k)).GrothendieckGroup ≃+ ℤ :=
  (abelianGrothendieckEquiv (FGModuleCat.{u} k)).trans
    (CategoryTheory.GrothendieckGroup.fgModuleRankEquiv k)

/-- The dimension equivalence is normalized on each actual object generator. -/
@[simp]
theorem fgModuleExactRankEquiv_class (V : FGModuleCat.{u} k) :
    fgModuleExactRankEquiv k
        ((abelianExactStructure (FGModuleCat.{u} k)).grothendieckClass V) =
      Module.finrank k V := by
  simp [fgModuleExactRankEquiv]

/-- The class of the one-dimensional vector space maps to one. -/
theorem fgModuleExactRankEquiv_self :
    fgModuleExactRankEquiv k
        ((abelianExactStructure (FGModuleCat.{u} k)).grothendieckClass (FGModuleCat.of k k)) =
      1 := by
  simp

end CategoryTheory.ExactCategory

attribute [colib_tag "COL-0020",
  colib_ref "WeibelKBook" "II, section 6.2, field paragraph (online chapter p. 48)"
    "adaptation"
    "Dimension on object classes for the canonical exact structure on finite modules over a field"]
  CategoryTheory.ExactCategory.fgModuleExactRankEquiv

attribute [colib_tag "COL-0020"]
  CategoryTheory.ExactCategory.fgModuleExactRankEquiv_class
  CategoryTheory.ExactCategory.fgModuleExactRankEquiv_self
