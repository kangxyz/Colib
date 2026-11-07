/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeExact
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveMonoidal
public import Colib.CategoryTheory.Monoidal.CoproductFunctor
public import Colib.CategoryTheory.Monoidal.CoreFunctor

/-!
Implementation provenance:
`Quillen/Aglib/Algebra/Category/ModuleCat/FiniteProjectiveBaseChangeMonoidal.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Direct-sum strong monoidal change of rings

The existing additive change-of-rings functor on actual finite projective right
modules preserves finite coproducts. Its strong monoidal comparisons are the
original initial and binary-coproduct comparisons. The actual core functor
therefore gives strong monoidal change of rings on the projective isomorphism
groupoids, retaining all original maps and coherence.

Rings are arbitrary unital, possibly noncommutative or zero. This interface uses
a common ring universe, matching the existing exact-functor K-theory interface.
-/

@[expose] public section
noncomputable section
open CategoryTheory Limits MonoidalCategory
universe u
namespace ModuleCat.FiniteProjective
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] categoryDirectSumMonoidal categoryDirectSumSymmetric
  directSumMonoidal directSumSymmetric
variable {R S T : Type u} [Ring R] [Ring S] [Ring T]

/-- Original change of rings is strong monoidal for the chosen direct sums. -/
@[instance_reducible]
def rightBaseChangeMonoidal (f : R →+* S) : (rightBaseChange f).Monoidal :=
  CoproductMonoidal.monoidal (rightBaseChange f)

attribute [local instance] rightBaseChangeMonoidal

/-- Original change of rings respects the chosen direct-sum braiding. -/
@[instance_reducible]
def rightBaseChangeBraided (f : R →+* S) : (rightBaseChange f).Braided where
  __ := rightBaseChangeMonoidal f
  __ := CoproductMonoidal.laxBraided (rightBaseChange f)

/-- The specified unit isomorphism is the original initial comparison. -/
def rightBaseChangeUnitIso (f : R →+* S) :
    (𝟙_ (Category.{u, u} Sᵐᵒᵖ)) ≅ (rightBaseChange f).obj (𝟙_ (Category.{u, u} Rᵐᵒᵖ)) :=
  Functor.Monoidal.εIso (rightBaseChange f)

/-- The specified tensor isomorphism is the original coproduct comparison. -/
def rightBaseChangeTensorIso (f : R →+* S) (P Q : Category.{u, u} Rᵐᵒᵖ) :
    (rightBaseChange f).obj P ⊗ (rightBaseChange f).obj Q ≅
      (rightBaseChange f).obj (P ⊗ Q) :=
  Functor.Monoidal.μIso (rightBaseChange f) P Q

/-- No replacement of the original initial comparison is made. -/
lemma rightBaseChangeUnitIso_hom (f : R →+* S) :
    (rightBaseChangeUnitIso f).hom = initialComparison (rightBaseChange f) := rfl

/-- No replacement of the original coproduct comparison is made. -/
lemma rightBaseChangeTensorIso_hom (f : R →+* S) (P Q : Category.{u, u} Rᵐᵒᵖ) :
    (rightBaseChangeTensorIso f P Q).hom = coprodComparison (rightBaseChange f) P Q := rfl

/-- The first coproduct inclusion retains its original base-changed arrow. -/
@[reassoc]
lemma rightBaseChangeTensorIso_inl (f : R →+* S) (P Q : Category.{u, u} Rᵐᵒᵖ) :
    coprod.inl ≫ (rightBaseChangeTensorIso f P Q).hom =
      (rightBaseChange f).map coprod.inl :=
  coprodComparison_inl _

/-- The second coproduct inclusion retains its original base-changed arrow. -/
@[reassoc]
lemma rightBaseChangeTensorIso_inr (f : R →+* S) (P Q : Category.{u, u} Rᵐᵒᵖ) :
    coprod.inr ≫ (rightBaseChangeTensorIso f P Q).hom =
      (rightBaseChange f).map coprod.inr :=
  coprodComparison_inr _

/-- The existing identity comparison respects the original direct-sum monoidal data. -/
instance rightBaseChangeId_isMonoidal : (rightBaseChangeId (R := R)).hom.IsMonoidal where
  unit := by
    change initialComparison (rightBaseChange (RingHom.id R)) ≫
      (rightBaseChangeId (R := R)).hom.app (⊥_ _) = 𝟙 (⊥_ _)
    apply Subsingleton.elim
  tensor P Q := by
    change coprodComparison (rightBaseChange (RingHom.id R)) P Q ≫
        (rightBaseChangeId (R := R)).hom.app (P ⨿ Q) =
      coprod.map ((rightBaseChangeId (R := R)).hom.app P)
        ((rightBaseChangeId (R := R)).hom.app Q) ≫ 𝟙 _
    apply coprod.hom_ext
    · simp
    · simp

/-- The existing composition comparison respects the original direct-sum monoidal data. -/
instance rightBaseChangeComp_isMonoidal (f : R →+* S) (g : S →+* T) :
    (rightBaseChangeComp f g).hom.IsMonoidal where
  unit := by
    change initialComparison (rightBaseChange g) ≫
      (rightBaseChange g).map (initialComparison (rightBaseChange f)) ≫
        (rightBaseChangeComp f g).hom.app (⊥_ _) =
      initialComparison (rightBaseChange (g.comp f))
    apply Subsingleton.elim
  tensor P Q := by
    change (coprodComparison (rightBaseChange g)
        ((rightBaseChange f).obj P) ((rightBaseChange f).obj Q) ≫
          (rightBaseChange g).map (coprodComparison (rightBaseChange f) P Q)) ≫
        (rightBaseChangeComp f g).hom.app (P ⨿ Q) =
      coprod.map ((rightBaseChangeComp f g).hom.app P)
        ((rightBaseChangeComp f g).hom.app Q) ≫
          coprodComparison (rightBaseChange (g.comp f)) P Q
    apply coprod.hom_ext
    · simp only [Category.assoc, coprodComparison_inl_assoc, coprod.inl_map_assoc,
        coprodComparison_inl]
      rw [← Functor.map_comp_assoc, coprodComparison_inl]
      exact (rightBaseChangeComp f g).hom.naturality (coprod.inl : P ⟶ P ⨿ Q)
    · simp only [Category.assoc, coprodComparison_inr_assoc, coprod.inr_map_assoc,
        coprodComparison_inr]
      rw [← Functor.map_comp_assoc, coprodComparison_inr]
      exact (rightBaseChangeComp f g).hom.naturality (coprod.inr : Q ⟶ P ⨿ Q)

/-- The functor on actual projective isomorphisms is the original core lift. -/
abbrev rightBaseChangeCore (f : R →+* S) : IsoCategory Rᵐᵒᵖ ⥤ IsoCategory Sᵐᵒᵖ :=
  (rightBaseChange f).core

/-- Strong monoidal change of rings on the actual projective isomorphism groupoids. -/
@[instance_reducible]
def rightBaseChangeCoreMonoidal (f : R →+* S) : (rightBaseChangeCore f).Monoidal :=
  inferInstance

/-- The core unit comparison has the original initial-comparison homomorphism. -/
lemma rightBaseChangeCore_ε_hom (f : R →+* S) :
    (Functor.LaxMonoidal.ε (rightBaseChangeCore f)).iso.hom =
      initialComparison (rightBaseChange f) := rfl

/-- The core tensor comparison has the original coproduct-comparison homomorphism. -/
lemma rightBaseChangeCore_μ_hom (f : R →+* S) (P Q : IsoCategory Rᵐᵒᵖ) :
    (Functor.LaxMonoidal.μ (rightBaseChangeCore f) P Q).iso.hom =
      coprodComparison (rightBaseChange f) P.of Q.of := rfl

/-- Forgetting core arrows recovers the original base-change functor exactly. -/
lemma rightBaseChangeCore_inclusion (f : R →+* S) :
    rightBaseChangeCore f ⋙ Core.inclusion _ = Core.inclusion _ ⋙ rightBaseChange f :=
  Functor.core_comp_inclusion _

/-- The original identity comparison induces the identity comparison on cores. -/
def rightBaseChangeCoreId : rightBaseChangeCore (RingHom.id R) ≅ 𝟭 (IsoCategory Rᵐᵒᵖ) :=
  (rightBaseChangeId (R := R)).core ≪≫ Functor.coreId _

/-- The original composition comparison induces the composition comparison on cores. -/
def rightBaseChangeCoreComp (f : R →+* S) (g : S →+* T) :
    rightBaseChangeCore f ⋙ rightBaseChangeCore g ≅ rightBaseChangeCore (g.comp f) :=
  (Functor.coreComp (rightBaseChange f) (rightBaseChange g)).symm ≪≫
    (rightBaseChangeComp f g).core

/-- The lifted original identity comparison is genuinely monoidal. -/
instance rightBaseChangeCoreId_isMonoidal :
    (rightBaseChangeCoreId (R := R)).hom.IsMonoidal := by
  dsimp only [rightBaseChangeCoreId, Iso.trans_hom]
  infer_instance

/-- The lifted original composition comparison is genuinely monoidal. -/
instance rightBaseChangeCoreComp_isMonoidal (f : R →+* S) (g : S →+* T) :
    (rightBaseChangeCoreComp f g).hom.IsMonoidal := by
  dsimp only [rightBaseChangeCoreComp, Iso.trans_hom, Iso.symm_hom]
  infer_instance

end ModuleCat.FiniteProjective
