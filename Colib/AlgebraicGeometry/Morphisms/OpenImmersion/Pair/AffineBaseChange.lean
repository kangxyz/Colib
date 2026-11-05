/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-!
# Fixed original open-pair base change over coefficient algebras

For a fixed original open immersion j into Spec R, each object of Under R has one specified
pullback of j. Original coefficient arrows induce the actual pullback lifts between those fixed
objects. Monicity proves strict identity and composition without identifying iterated pullback
objects. At the identity algebra the original projection is an actual isomorphism, not an equality
with the independently chosen pullback object.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.AffineOpenPair

variable {R : CommRingCat.{u}} {U : AlgebraicGeometry.Scheme.{u}}
    (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The fixed original open pulled back over one specified coefficient algebra. -/
abbrev openSpace (a : Under R) := pullback j (Spec.map a.hom)

/-- The actual second pullback projection is the specified new open immersion. -/
abbrev inclusion (a : Under R) : openSpace j a ⟶ Spec a.right :=
  pullback.snd j (Spec.map a.hom)

/-- The original first pullback projection retains the given open scheme. -/
abbrev projection (a : Under R) : openSpace j a ⟶ U :=
  pullback.fst j (Spec.map a.hom)

/-- The actual lift induced by an arrow between the fixed coefficient algebras. -/
def openMap {a b : Under R} (f : a ⟶ b) : openSpace j b ⟶ openSpace j a :=
  pullback.lift (projection j b) (inclusion j b ≫ Spec.map f.right) (by
    rw [Category.assoc, ← Spec.map_comp, Under.w f]
    exact pullback.condition)

omit [IsOpenImmersion j] in
/-- The original lift retains the original open-side projection exactly. -/
@[reassoc] theorem openMap_projection {a b : Under R} (f : a ⟶ b) :
    openMap j f ≫ projection j a = projection j b :=
  pullback.lift_fst _ _ _

omit [IsOpenImmersion j] in
/-- The original lift gives precisely the coefficient-map open-pair square. -/
@[reassoc] theorem openMap_inclusion {a b : Under R} (f : a ⟶ b) :
    openMap j f ≫ inclusion j a = inclusion j b ≫ Spec.map f.right :=
  pullback.lift_snd _ _ _

/-- The specified pullback objects make the original identity map literally the identity. -/
theorem openMap_id (a : Under R) : openMap j (𝟙 a) = 𝟙 (openSpace j a) := by
  apply (cancel_mono (inclusion j a)).1
  simpa using openMap_inclusion j (𝟙 a)

/-- Composition uses the same fixed source and target pullbacks and the original coefficient maps.
-/
theorem openMap_comp {a b c : Under R} (f : a ⟶ b) (g : b ⟶ c) :
    openMap j (f ≫ g) = openMap j g ≫ openMap j f := by
  apply (cancel_mono (inclusion j a)).1
  simp only [openMap_inclusion, Category.assoc, openMap_inclusion_assoc,
    Under.comp_right, Spec.map_comp]

/-- At the identity algebra the actual original projection is an isomorphism. -/
def identityProjectionIso : openSpace j (Under.mk (𝟙 R)) ≅ U :=
  by
    have : IsIso (Spec.map (𝟙 R)) := by rw [Spec.map_id]; infer_instance
    have : IsIso (projection j (Under.mk (𝟙 R))) := by
      change IsIso (pullback.fst j (Spec.map (𝟙 R)))
      infer_instance
    exact asIso (projection j (Under.mk (𝟙 R)))

omit [IsOpenImmersion j] in
/-- The identity-base-change iso retains the whole original inclusion square. -/
theorem identityProjectionIso_inclusion :
    (identityProjectionIso j).hom ≫ j = inclusion j (Under.mk (𝟙 R)) := by
  change projection j (Under.mk (𝟙 R)) ≫ j = _
  calc
    _ = inclusion j (Under.mk (𝟙 R)) ≫ Spec.map (𝟙 R) := pullback.condition
    _ = _ := by
      rw [Spec.map_id]
      exact Category.comp_id (inclusion j (Under.mk (𝟙 R)))

end AlgebraicGeometry.Scheme.AffineOpenPair

attribute [colib_tag "COL-0149",
  stacks 01JY "Open immersions remain open under base change; chosen lift formulas are explicit"]
  AlgebraicGeometry.Scheme.AffineOpenPair.openSpace
  AlgebraicGeometry.Scheme.AffineOpenPair.inclusion
  AlgebraicGeometry.Scheme.AffineOpenPair.projection
  AlgebraicGeometry.Scheme.AffineOpenPair.openMap
  AlgebraicGeometry.Scheme.AffineOpenPair.openMap_projection
  AlgebraicGeometry.Scheme.AffineOpenPair.openMap_inclusion
  AlgebraicGeometry.Scheme.AffineOpenPair.openMap_id
  AlgebraicGeometry.Scheme.AffineOpenPair.openMap_comp
  AlgebraicGeometry.Scheme.AffineOpenPair.identityProjectionIso
  AlgebraicGeometry.Scheme.AffineOpenPair.identityProjectionIso_inclusion
