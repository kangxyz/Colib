/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveBaseChange

/-!
Implementation provenance: Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd,
`Quillen/Aglib/Algebra/Category/ModuleCat/FiniteProjectiveBaseChangeExact.lean`.
The original hypotheses and maps are retained.

# Additivity and exactness of change of rings

Matrix change of rings and the actual-image equivalence are additive. The
inverse equivalence is additive by faithfulness of the forward equivalence.
Every conflation of finite projective modules splits; preserving this explicit
splitting proves exactness for arbitrary ring homomorphisms.
-/
@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section

universe u v

open CategoryTheory CategoryTheory.Idempotents

namespace Matrix.RightModule

variable {R : Type u} {S : Type v} [Ring R] [Ring S]

instance freeCategoryPreadditive : Preadditive (FreeCategory R) where
  homGroup P Q := inferInstanceAs (AddCommGroup (Matrix (Fin Q.rank) (Fin P.rank) R))
  add_comp _ _ _ f g h := Matrix.mul_add h f g
  comp_add _ _ _ f g h := Matrix.add_mul g h f

instance freeBaseChangeAdditive (f : R →+* S) : (freeBaseChange f).Additive where
  map_add := by intros; funext i j; exact f.map_add _ _

instance baseChangeAdditive (f : R →+* S) : (baseChange f).Additive where
  map_add := by intros; apply Karoubi.Hom.ext; funext i j; exact f.map_add _ _

instance imageFunctorAdditive : (imageFunctor (R := R)).Additive where
  map_add := by
    intros P Q f g
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact Matrix.add_mulVec f.f g.f x.val

/-- The forward equivalence is additive by the explicit sum formula for matrix action. -/
instance imageEquivalenceFunctorAdditive : (imageEquivalence (R := R)).functor.Additive :=
  imageFunctorAdditive

/-- Additivity of the inverse follows from the proved additive, faithful forward functor. -/
instance imageEquivalenceInverseAdditive : (imageEquivalence (R := R)).inverse.Additive :=
  Equivalence.inverse_additive imageEquivalence

end Matrix.RightModule

namespace ModuleCat.FiniteProjective

variable {R : Type u} {S : Type v} [Ring R] [Ring S]

instance rightBaseChangeAdditive (f : R →+* S) : (rightBaseChange f).Additive :=
  inferInstanceAs (Matrix.RightModule.imageEquivalence.inverse ⋙ Matrix.RightModule.baseChange f ⋙
    Matrix.RightModule.imageEquivalence.functor).Additive

/-- The actual change-of-rings functor preserves the inherited exact structures. -/
def rightBaseChangeExact (f : R →+* S) :
    ExactFunctor (exactStructure.{u,u} Rᵐᵒᵖ) (exactStructure.{v,v} Sᵐᵒᵖ) where
  toFunctor := rightBaseChange f
  map_conflation K hK :=
    (conflation_iff_nonempty_splitting Sᵐᵒᵖ (K.map (rightBaseChange f))).mpr
      ⟨(splittingOfConflation Rᵐᵒᵖ K hK).map (rightBaseChange f)⟩

end ModuleCat.FiniteProjective
