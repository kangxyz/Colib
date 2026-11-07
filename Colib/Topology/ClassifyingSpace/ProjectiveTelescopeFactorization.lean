/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.ProjectiveTelescope
public import Colib.CategoryTheory.Monoidal.TensorFunctor.Factorization

/-!
Adapted from `Quillen/KTheory/Plus/ProjectiveTelescopeFactorization.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original projective
complements, stage maps and coefficient transports are retained.
 # Genuine finite-stage factorization for projective telescope translations -/

@[expose] public section
noncomputable section
open CategoryTheory MonoidalCategory Grothendieck
universe u
namespace ModuleCat.FiniteProjective
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal directSumSymmetric
variable (R : Type u) [Ring R]

/-- Iterated original right rank-one additions agree with the labelled free module. -/
def rightIterationFreeIso : ∀ n : ℕ,
    EndofunctorTelescope.iterate (tensorRight (freeIso Rᵐᵒᵖ 1)) n ≅
      tensorRight (freeIso Rᵐᵒᵖ n)
  | 0 => (rightUnitorNatIso (IsoCategory Rᵐᵒᵖ)).symm ≪≫
      TranslationTelescope.rightParameterIso (freeIsoZero Rᵐᵒᵖ)
  | n + 1 => Functor.isoWhiskerRight (rightIterationFreeIso n)
      (tensorRight (freeIso Rᵐᵒᵖ 1)) ≪≫
      TranslationTelescope.rightTensorIso (freeIso Rᵐᵒᵖ n) (freeIso Rᵐᵒᵖ 1) ≪≫
      TranslationTelescope.rightParameterIso
        ((β_ (freeIso Rᵐᵒᵖ n) (freeIso Rᵐᵒᵖ 1)) ≪≫ freeIsoSucc Rᵐᵒᵖ n)

/-- An actual complement gives a genuine factorization of the original right iteration. -/
def rightIterationComplementIso (P Q : IsoCategory Rᵐᵒᵖ) (n : ℕ)
    (f : P ⊗ Q ≅ freeIso Rᵐᵒᵖ n) :
    EndofunctorTelescope.iterate (tensorRight (freeIso Rᵐᵒᵖ 1)) n ≅
      tensorRight (C := IsoCategory Rᵐᵒᵖ) Q ⋙ tensorLeft (C := IsoCategory Rᵐᵒᵖ) P :=
  rightIterationFreeIso R n ≪≫ TranslationTelescope.rightParameterIso f.symm ≪≫
    TranslationTelescope.rightSumFactorization P Q

/-- Every projective parameter yields an actual finite-stage factorization. -/
theorem exists_rightIterationComplementIso (P : IsoCategory Rᵐᵒᵖ) :
    ∃ (n : ℕ) (Q : IsoCategory Rᵐᵒᵖ), Nonempty
      (EndofunctorTelescope.iterate (tensorRight (freeIso Rᵐᵒᵖ 1)) n ≅
        tensorRight (C := IsoCategory Rᵐᵒᵖ) Q ⋙ tensorLeft (C := IsoCategory Rᵐᵒᵖ) P) := by
  obtain ⟨n, Q, ⟨f⟩⟩ := exists_complement_iso_freeIso Rᵐᵒᵖ P
  exact ⟨n, Q, ⟨rightIterationComplementIso R P Q n f⟩⟩

/-- The chosen finite right step factors through left translation in the actual
common-universe stage category. -/
def projectiveStageFactorizationIso (P Q : IsoCategory Rᵐᵒᵖ) (k n : ℕ)
    (f : P ⊗ Q ≅ freeIso Rᵐᵒᵖ k) :
    ((projectiveTelescopeDiagram R).map (homOfLE (Nat.le_add_right n k))).toFunctor ≅
      (AsSmall.down.{_, _, 0} ⋙ tensorRight (C := IsoCategory Rᵐᵒᵖ) Q ⋙ AsSmall.up.{_, _, 0}) ⋙
        (AsSmall.down.{_, _, 0} ⋙ tensorLeft (C := IsoCategory Rᵐᵒᵖ) P ⋙ AsSmall.up.{_, _, 0}) := by
  change (AsSmall.down.{_, _, 0} ⋙
    EndofunctorTelescope.iterate (tensorRight (freeIso Rᵐᵒᵖ 1)) (n + k - n) ⋙
      AsSmall.up.{_, _, 0}) ≅ _
  rw [Nat.add_sub_cancel_left]
  exact Functor.isoWhiskerLeft AsSmall.down.{_, _, 0}
    (Functor.isoWhiskerRight (rightIterationComplementIso R P Q k f) AsSmall.up.{_, _, 0})

/-- The actual telescope stabilization arrow followed by the complement
factorization gives a specified transformation through the original left action. -/
def projectiveStageFactorizationNatTrans (P Q : IsoCategory Rᵐᵒᵖ) (k n : ℕ)
    (f : P ⊗ Q ≅ freeIso Rᵐᵒᵖ k) :
    Grothendieck.ι (projectiveTelescopeDiagram R) n ⟶
      (AsSmall.down.{_, _, 0} ⋙ tensorRight (C := IsoCategory Rᵐᵒᵖ) Q ⋙ AsSmall.up.{_, _, 0}) ⋙
        Grothendieck.ι (projectiveTelescopeDiagram R) (n + k) ⋙
          projectiveTelescopeTranslation R P := by
  let a := Grothendieck.ιNatTrans (F := projectiveTelescopeDiagram R)
    (homOfLE (Nat.le_add_right n k))
  let b := Functor.isoWhiskerRight (projectiveStageFactorizationIso R P Q k n f)
    (Grothendieck.ι (projectiveTelescopeDiagram R) (n + k))
  refine a ≫ b.hom ≫ eqToHom ?_
  rw [projectiveTelescopeTranslation_stage]
  rfl

end ModuleCat.FiniteProjective
