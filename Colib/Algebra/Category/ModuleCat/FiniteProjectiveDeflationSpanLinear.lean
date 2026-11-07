/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveDeflationEntry
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionSpanLinear
public import Colib.CategoryTheory.ExactCategory.ExtensionDeflationSpan

/-!
Implementation provenance:
`Quillen/Algebra/Category/ModuleCat/FiniteProjectiveDeflationSpanLinear.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Equivariance of the actual original-span pullback projections -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalLeftAction
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal inflationDirectSumAction
attribute [local instance] extensionFiberDirectSumAction extensionDeflationEntryLinear

/-- Pullbacks of the original admissible deflations exist. -/
local instance deflationSpanLinearHasPullback {X Y : Category.{u, u} R} (f : X ⟶ Y)
    (p : (exactStructure R).ExtensionFiber Y) : HasPullback p.of.obj.hom f :=
  (exactStructure R).deflation.hasPullback f p.of.property

/-- The original span-lift natural arrow commutes with adding projectives.
The genuine pullback lineator is used on the transported fixed deflation. -/
lemma extensionDeflationSpan_linear {X Y : Category.{u, u} R}
    (s : Span (exactStructure R).deflation (exactStructure R).inflation X Y)
    (S : IsoCategory R) (p : (exactStructure R).ExtensionFiber Y) :
    let := extensionSpanTransportLinear R s
    (extensionDeflationAddIso R X S
      (((exactStructure R).extensionSpanTransport s).obj p)).hom ≫
      ((exactStructure R).extensionDeflationEntry X).map
        (Functor.LaxLeftLinear.μₗ ((exactStructure R).extensionSpanTransport s) S p) ≫
      (exactStructure R).extensionDeflationSpanHom s (S ⊙ₗ p) =
    S ⊴ₗ (exactStructure R).extensionDeflationSpanHom s p ≫
      (extensionDeflationAddIso R Y S p).hom := by
  let := extensionSpanTransportLinear R s
  apply (exactStructure R).extensionTotalMiddle.map_injective
  change 𝟙 _ ≫ (𝟙 _ ≫ extensionPullbackAddHom R s.r S p) ≫
      pullback.fst (S ⊙ₗ p).of.obj.hom s.r =
    ((𝟙 S.of ▷ _) ≫ S.of ◁ pullback.fst p.of.obj.hom s.r) ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id, id_whiskerRight]
  exact extensionPullbackAddHom_fst R s.r S p

end ModuleCat.FiniteProjective
