/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveMonoidal
public import Colib.CategoryTheory.Monoidal.TranslationTelescope

/-!
Adapted from `Quillen/KTheory/Plus/ProjectiveTelescope.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the original
functors, associators and category universes.
 # The precompletion telescope of finite projective right modules

This sequence repeatedly adds the original free rank-one right module. Its left
translations are actual functors on the telescope, constructed from associators.
No homology equivalence of these translations is asserted here.
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory Grothendieck
namespace ModuleCat.FiniteProjective
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal
variable (R : Type u) [Ring R]

/-- The original right-addition sequence of projective right modules. -/
def projectiveTelescopeDiagram : ℕ ⥤ Cat.{u + 1, u + 1} :=
  TranslationTelescope.diagram (freeIso Rᵐᵒᵖ 1)

/-- The actual Grothendieck telescope before group completion. -/
abbrev ProjectiveTelescope := Grothendieck (projectiveTelescopeDiagram R)

/-- Left addition of a fixed projective right module on the precompletion telescope. -/
def projectiveTelescopeTranslation (P : IsoCategory Rᵐᵒᵖ) :
    ProjectiveTelescope R ⥤ ProjectiveTelescope R :=
  TranslationTelescope.leftTranslation (freeIso Rᵐᵒᵖ 1) P

/-- Each original stage retains its precise left-addition functor. -/
theorem projectiveTelescopeTranslation_stage (P : IsoCategory Rᵐᵒᵖ) (n : ℕ) :
    Grothendieck.ι (projectiveTelescopeDiagram R) n ⋙ projectiveTelescopeTranslation R P =
      (AsSmall.down ⋙ tensorLeft P ⋙ AsSmall.up) ⋙
        Grothendieck.ι (projectiveTelescopeDiagram R) n :=
  TranslationTelescope.inclusion_leftTranslation _ _ _

/-- The distinguished vertex is the original zero module at stage zero. -/
def projectiveTelescopeBase : ProjectiveTelescope R :=
  ⟨0, AsSmall.up.obj (𝟙_ (IsoCategory Rᵐᵒᵖ))⟩

/-- Its translate has the original unitor isomorphism to the projective vertex. -/
def projectiveTelescopeTranslationBaseIso (P : IsoCategory Rᵐᵒᵖ) :
    (projectiveTelescopeTranslation R P).obj (projectiveTelescopeBase R) ≅
      (⟨0, AsSmall.up.obj P⟩ : ProjectiveTelescope R) :=
  TranslationTelescope.leftTranslationUnitIso _ _

end ModuleCat.FiniteProjective
