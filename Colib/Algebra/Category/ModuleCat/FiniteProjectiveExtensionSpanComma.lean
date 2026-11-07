/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveFixedFiberEntry
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionSpanTransport
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionCartesian
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveDeflationSpanLinear

/-!
Implementation provenance:
`Quillen/KTheory/Plus/ProjectiveExtensionSpanComma.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Original Q-span transitions and the actual localized fiber entries -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal inflationDirectSumAction
attribute [local instance] extensionFiberDirectSumAction extensionDeflationEntryLinear

/-- The original pullback projection, with the projective denominator unchanged,
is the component of the localized structured-comma comparison. -/
def localizedFixedExtensionSpanHom {X Y : Category.{u, u} R}
    (s : Span (exactStructure R).deflation (exactStructure R).inflation X Y)
    (U : LocalizedFixedExtensionCategory R Y) :
    ((localizedFixedExtensionEntry R X).obj ((localizedExtensionSpanTransport R s).obj U)).right ⟶
      ((localizedFixedExtensionEntry R Y).obj U).right :=
  localizedExtensionOriginalHom R U.obj.1
    ((exactStructure R).extensionDeflationSpanHom s U.obj.2)

/-- The original contravariant Q-span transition commutes with fixed-fiber entries
up to the actual localized pullback-projection natural arrow. -/
def localizedFixedExtensionSpanComma {X Y : Category.{u, u} R}
    (s : Span (exactStructure R).deflation (exactStructure R).inflation X Y) :
    localizedExtensionSpanTransport R s ⋙ localizedFixedExtensionEntry R X ⟶
      localizedFixedExtensionEntry R Y ⋙ StructuredArrow.map
        (T := localizedExtensionProjection R)
        (QConstruction.mkHom (exactStructure R).deflation (exactStructure R).inflation s) where
  app U := StructuredArrow.homMk (localizedFixedExtensionSpanHom R s U) (by
    change ((exactStructure R).qIsoOfIso ((exactStructure R).extensionOfDeflationQuotientIso
      (((exactStructure R).extensionSpanTransport s).obj U.obj.2).of)).inv ≫
      (localizedExtensionProjection R).map (localizedExtensionOriginalHom R U.obj.1
        ((exactStructure R).extensionDeflationSpanHom s U.obj.2)) = _
    rw [localizedExtensionProjection_originalHom]
    exact (exactStructure R).extensionDeflationSpanHom_over s U.obj.2)
  naturality {U V} g := by
    let := extensionSpanTransportLinear R s
    apply StructuredArrow.hom_ext
    obtain ⟨r, rfl⟩ := GroupCompletion.ActionLocalization.mkHom_surjective U.obj V.obj g
    change ((localizedFixedExtensionEntry R X).map
      ((localizedExtensionSpanTransport R s).map
        (GroupCompletion.Localization.mkHom r.denom r.map.1 r.map.2))).right ≫
      localizedExtensionOriginalHom R V.obj.1
        ((exactStructure R).extensionDeflationSpanHom s V.obj.2) =
      localizedExtensionOriginalHom R U.obj.1
        ((exactStructure R).extensionDeflationSpanHom s U.obj.2) ≫
      ((localizedFixedExtensionEntry R Y).map
        (GroupCompletion.Localization.mkHom r.denom r.map.1 r.map.2)).right
    rw [localizedExtensionSpanTransport_mkHom, localizedFixedExtensionEntry_map_mkHom,
      localizedFixedExtensionEntry_map_mkHom]
    simp only [localizedExtensionOriginalHom, GroupCompletion.Localization.mkHom]
    rw [GroupCompletion.ActionLocalization.mkHom_comp_ofHom,
      GroupCompletion.ActionLocalization.ofHom_comp_mkHom]
    apply congrArg GroupCompletion.ActionLocalization.mkHom
    congr 1
    apply Prod.ext
    · change r.map.1 ≫ 𝟙 _ = (r.denom ◁ 𝟙 U.obj.1) ≫ r.map.1
      simp
    · change ((extensionDeflationAddIso R X r.denom
          (((exactStructure R).extensionSpanTransport s).obj U.obj.2)).hom ≫
          ((exactStructure R).extensionDeflationEntry X).map
            (Functor.LaxLeftLinear.μₗ ((exactStructure R).extensionSpanTransport s)
              r.denom U.obj.2 ≫ ((exactStructure R).extensionSpanTransport s).map r.map.2)) ≫
          (exactStructure R).extensionDeflationSpanHom s V.obj.2 =
        r.denom ⊴ₗ (exactStructure R).extensionDeflationSpanHom s U.obj.2 ≫
          ((extensionDeflationAddIso R Y r.denom U.obj.2).hom ≫
            ((exactStructure R).extensionDeflationEntry Y).map r.map.2)
      have hn := ((exactStructure R).extensionDeflationSpanNatTrans s).naturality r.map.2
      have hl := extensionDeflationSpan_linear R s r.denom U.obj.2
      change ((exactStructure R).extensionDeflationEntry X).map
          (((exactStructure R).extensionSpanTransport s).map r.map.2) ≫
          (exactStructure R).extensionDeflationSpanHom s V.obj.2 =
        (exactStructure R).extensionDeflationSpanHom s (r.denom ⊙ₗ U.obj.2) ≫
          ((exactStructure R).extensionDeflationEntry Y).map r.map.2 at hn
      have hn' := congrArg (fun k ↦ (extensionDeflationAddIso R X r.denom
        (((exactStructure R).extensionSpanTransport s).obj U.obj.2)).hom ≫
        ((exactStructure R).extensionDeflationEntry X).map
          (Functor.LaxLeftLinear.μₗ ((exactStructure R).extensionSpanTransport s)
            r.denom U.obj.2) ≫ k) hn
      have hl' := congrArg
        (fun k ↦ k ≫ ((exactStructure R).extensionDeflationEntry Y).map r.map.2) hl
      simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      simp only [Category.assoc] at hn' hl'
      exact hn'.trans hl'

end ModuleCat.FiniteProjective
