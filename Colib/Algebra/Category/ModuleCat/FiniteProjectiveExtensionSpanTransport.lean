/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionSpanLinear
public import Colib.CategoryTheory.GroupCompletion.LocalizationFunctoriality

/-!
Implementation provenance:
`Quillen/KTheory/Plus/ProjectiveExtensionSpanTransport.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The actual transport and its representative formulas are extracted below their
classifying-space weak-equivalence theorem.
 # The original localized Q-span extension transport -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]
attribute [local instance] directSumMonoidal directSumSymmetric extensionFiberDirectSumAction

/-- The actual common-denominator localization of the original Q-span transport. -/
def localizedExtensionSpanTransport {X Y : Category.{u, u} R}
    (s : Span (exactStructure R).deflation (exactStructure R).inflation X Y) :
    GroupCompletion.Localization (IsoCategory R) ((exactStructure R).ExtensionFiber Y) ⥤
      GroupCompletion.Localization (IsoCategory R) ((exactStructure R).ExtensionFiber X) := by
  letI := extensionSpanTransportLinear R s
  exact GroupCompletion.Localization.actedMapFunctor ((exactStructure R).extensionSpanTransport s)

/-- The actual localized transport fixes the denominator object. -/
@[simp]
theorem localizedExtensionSpanTransport_obj {X Y : Category.{u, u} R}
    (s : Span (exactStructure R).deflation (exactStructure R).inflation X Y)
    (A : GroupCompletion.Localization (IsoCategory R) ((exactStructure R).ExtensionFiber Y)) :
    (localizedExtensionSpanTransport R s).obj A =
      ⟨(A.obj.1, ((exactStructure R).extensionSpanTransport s).obj A.obj.2)⟩ := rfl

/-- Localization retains the original denominator and the original span-transport lineator. -/
theorem localizedExtensionSpanTransport_mkHom {X Y : Category.{u, u} R}
    (s : Span (exactStructure R).deflation (exactStructure R).inflation X Y)
    {A B : IsoCategory R × (exactStructure R).ExtensionFiber Y}
    (T : IsoCategory R) (f : T ⊗ A.1 ⟶ B.1) (g : T ⊙ₗ A.2 ⟶ B.2) :
    letI := extensionSpanTransportLinear R s
    (localizedExtensionSpanTransport R s).map (GroupCompletion.Localization.mkHom T f g) =
      GroupCompletion.Localization.mkHom
        (X := (A.1, ((exactStructure R).extensionSpanTransport s).obj A.2))
        (Y := (B.1, ((exactStructure R).extensionSpanTransport s).obj B.2)) T f
        (Functor.LaxLeftLinear.μₗ ((exactStructure R).extensionSpanTransport s) T A.2 ≫
          ((exactStructure R).extensionSpanTransport s).map g) := by
  let := extensionSpanTransportLinear R s
  exact GroupCompletion.Localization.actedMapFunctor_mkHom
    ((exactStructure R).extensionSpanTransport s) T f g

end ModuleCat.FiniteProjective
