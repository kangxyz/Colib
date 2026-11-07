/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.TranslationTelescopeFinite
public import Colib.Topology.LocalCoefficients.SquareHomology
public import Colib.Topology.LocalCoefficients.TelescopeHomologyDiagram

/-!
Adapted from `Quillen/Topology/LocalCoefficients/TelescopeTranslation.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual original
stage arrows, finite support and coefficient corrections.
 # Original finite-stage action maps commute with actual stabilization transport -/

@[expose] public section

open CategoryTheory.Grothendieck.Telescope
open FundamentalGroupoid.LocalCoefficients

noncomputable section
open CategoryTheory MonoidalCategory
universe u v
namespace CategoryTheory.MonoidalCategory.TranslationTelescope
open FundamentalGroupoid.LocalCoefficients Grothendieck.Telescope
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (e P : C)

/-- The original left tensor functor in the common-universe stage category. -/
def stageLeftFunctor : AsSmall.{0} C ⥤ AsSmall.{0} C :=
  AsSmall.down ⋙ tensorLeft P ⋙ AsSmall.up

/-- The actual stage action square of continuous maps. -/
theorem stageTranslation_square (n : ℕ) :
    (classifyingSpaceMap (leftTranslation e P)).hom.comp
        (classifyingSpaceMap (Grothendieck.ι (diagram e) n)).hom =
      (classifyingSpaceMap (Grothendieck.ι (diagram e) n)).hom.comp
        (classifyingSpaceMap (stageLeftFunctor P)).hom := by
  change (classifyingSpaceMap (Grothendieck.ι (diagram e) n) ≫
    classifyingSpaceMap (leftTranslation e P)).hom =
    (classifyingSpaceMap (stageLeftFunctor P) ≫
      classifyingSpaceMap (Grothendieck.ι (diagram e) n)).hom
  rw [← classifyingSpaceMap_comp, ← classifyingSpaceMap_comp, inclusion_leftTranslation]
  rfl

/-- The actual finite-prefix action square of continuous maps. -/
theorem prefixTranslation_square (n : ℕ) :
    (classifyingSpaceMap (leftTranslation e P)).hom.comp
        (classifyingSpaceMap (prefixInclusion (diagram e) n)).hom =
      (classifyingSpaceMap (prefixInclusion (diagram e) n)).hom.comp
        (classifyingSpaceMap (prefixTranslation e P n)).hom := by
  change (classifyingSpaceMap (prefixInclusion (diagram e) n) ≫
    classifyingSpaceMap (leftTranslation e P)).hom =
    (classifyingSpaceMap (prefixTranslation e P n) ≫
      classifyingSpaceMap (prefixInclusion (diagram e) n)).hom
  rw [← classifyingSpaceMap_comp, ← classifyingSpaceMap_comp, prefixTranslation_inclusion]

variable (A : System.{max u v, max u v} (ClassifyingSpace (Model e))) (d : ℕ)

/-- The original finite-stage left action with its exact total-action coefficient conversion. -/
def stageTranslationHomology (n : ℕ) :=
  squareHomologyMap (classifyingSpaceMap (stageLeftFunctor P)).hom
    (classifyingSpaceMap (Grothendieck.ι (diagram e) n)).hom
    (classifyingSpaceMap (Grothendieck.ι (diagram e) n)).hom
    (classifyingSpaceMap (leftTranslation e P)).hom (stageTranslation_square e P n) A d

/-- The original finite-prefix left action with the same canonical coefficient conversion. -/
def prefixTranslationHomology (n : ℕ) :=
  squareHomologyMap (classifyingSpaceMap (prefixTranslation e P n)).hom
    (classifyingSpaceMap (prefixInclusion (diagram e) n)).hom
    (classifyingSpaceMap (prefixInclusion (diagram e) n)).hom
    (classifyingSpaceMap (leftTranslation e P)).hom (prefixTranslation_square e P n) A d

/-- The last-stage comparison is natural for the actual source and target systems. -/
@[reassoc]
theorem stageToPrefixHomology_translation (n : ℕ) :
    stageTranslationHomology e P A d n ≫ stageToPrefixHomology (diagram e) n A d =
      stageToPrefixHomology (diagram e) n
        (pullback (classifyingSpaceMap (leftTranslation e P)).hom A) d ≫
          prefixTranslationHomology e P A d n := by
  apply squareHomologyMap_naturality
  symm
  change (classifyingSpaceMap
    (Grothendieck.FiniteTelescope.inclusion (diagram e) n (Fin.last n)) ≫
      classifyingSpaceMap (prefixTranslation e P n)).hom =
    (classifyingSpaceMap (stageLeftFunctor P) ≫ classifyingSpaceMap
      (Grothendieck.FiniteTelescope.inclusion (diagram e) n (Fin.last n))).hom
  rw [← classifyingSpaceMap_comp, ← classifyingSpaceMap_comp, lastInclusion_prefixTranslation]
  rfl

/-- Original prefix actions commute with the original finite-prefix transition maps. -/
@[reassoc]
theorem prefixTranslationHomology_transition {n m : ℕ} (h : n ≤ m) :
    prefixTranslationHomology e P A d n ≫ prefixHomologyTransition (diagram e) h A d =
      prefixHomologyTransition (diagram e) h
        (pullback (classifyingSpaceMap (leftTranslation e P)).hom A) d ≫
          prefixTranslationHomology e P A d m := by
  apply squareHomologyMap_naturality
  change (classifyingSpaceMap (prefixTranslation e P n) ≫
    classifyingSpaceMap (prefixTransition (diagram e) h)).hom =
    (classifyingSpaceMap (prefixTransition (diagram e) h) ≫
      classifyingSpaceMap (prefixTranslation e P m)).hom
  rw [← classifyingSpaceMap_comp, ← classifyingSpaceMap_comp, prefixTranslation_transition]

/-- The original finite-stage action commutes with the original stabilization map,
including the actual stabilization-track coefficient conversion on both sides. -/
@[reassoc]
theorem stageTranslationHomology_transition {n m : ℕ} (h : n ≤ m) :
    stageTranslationHomology e P A d n ≫ stageHomologyTransition (diagram e) h A d =
      stageHomologyTransition (diagram e) h
        (pullback (classifyingSpaceMap (leftTranslation e P)).hom A) d ≫
          stageTranslationHomology e P A d m := by
  let := stageToPrefixHomology_isIso (diagram e) m A d
  apply (cancel_mono (stageToPrefixHomology (diagram e) m A d)).mp
  rw [Category.assoc, ← stageToPrefixHomology_transition,
    ← Category.assoc, stageToPrefixHomology_translation,
    Category.assoc, prefixTranslationHomology_transition,
    ← Category.assoc, stageToPrefixHomology_transition,
    Category.assoc, ← stageToPrefixHomology_translation, ← Category.assoc]

end CategoryTheory.MonoidalCategory.TranslationTelescope
