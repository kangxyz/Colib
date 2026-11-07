/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.AlgebraicGeometry.Scheme.Restriction
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic

/-!
# The actual exact inclusion of vector bundles into coherent sheaves

On a locally noetherian scheme, the native finite locally free module sheaves are coherent.
The comparison is the literal lift of their full inclusion, with unchanged objects and maps.
Its compatibility with actual open restriction is consequently a natural isomorphism whose
components are identities.

Implementation provenance: the categorical comparison underlying
`Quillen/AlgebraicGeometry/Scheme/Comparison/KToG.lean` at `c561118b` and
`Aglib/AlgebraicGeometry/Modules/LocallyFree/Coherent.lean` at
`2c34f185fa859e862661f939cd216b07bcccfb26`. The native Stacks coherence predicate and
native vector-bundle category replace the earlier Aglib models.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- The literal full inclusion of native vector bundles into native coherent sheaves. -/
def vectorBundleToCoherent : X.Vect ⥤ SheafOfModules.CoherentModules X.ringCatSheaf :=
  ObjectProperty.lift _ (ObjectProperty.ι _) fun M => by
    have := M.property
    exact Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X M.obj

instance vectorBundleToCoherent_additive : (vectorBundleToCoherent X).Additive := by
  dsimp [vectorBundleToCoherent]
  infer_instance

@[simp]
theorem vectorBundleToCoherent_obj (M : X.Vect) :
    ((vectorBundleToCoherent X).obj M).obj = M.obj := rfl

@[simp]
theorem vectorBundleToCoherent_map {M N : X.Vect} (f : M ⟶ N) :
    ((vectorBundleToCoherent X).map f).hom = f.hom := rfl

/-- The actual vector-bundle inclusion is exact for the native exact structures. -/
def vectorBundleToCoherentExact :
    ExactFunctor (vectorBundleExactStructure X) (coherentExactStructure X) where
  toFunctor := vectorBundleToCoherent X
  map_conflation _S hS := (coherent_shortExact_iff_map X _).2 hS

variable {X} {U : Scheme.{u}} [IsLocallyNoetherian U]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- The comparison commutes with actual open restriction, by identity components. -/
def vectorBundleToCoherentRestrictIso :
    vectorBundleToCoherent X ⋙ coherentRestrict j ≅
      vectorBundleRestrict j ⋙ vectorBundleToCoherent U :=
  Iso.refl _

@[simp]
theorem vectorBundleToCoherentRestrictIso_hom_app (M : X.Vect) :
    ((vectorBundleToCoherentRestrictIso j).hom.app M).hom =
      𝟙 ((restrictFunctor j).obj M.obj) := rfl

@[simp]
theorem vectorBundleToCoherentRestrictIso_inv_app (M : X.Vect) :
    ((vectorBundleToCoherentRestrictIso j).inv.app M).hom =
      𝟙 ((restrictFunctor j).obj M.obj) := rfl

end AlgebraicGeometry.Scheme.Modules
