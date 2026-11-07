/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.CategoryTheory.Center.Linear
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Scalar natural automorphisms of linear categories

For a ring `R` and an `R`-linear preadditive category `C`, scalar units give
natural automorphisms of the identity through `Linear.toCatCenter` and
`Aut.unitsEndEquivAut`. Their components are scalar multiples of identity
morphisms, and ordinary `R`-linear functors preserve those components.

For an essentially small `C`, full faithfulness lifts the same automorphism
through the original realization of its chosen `SmallModel`. This construction
does not require a linear structure on the model.

The exact-category scalar-operation consumer uses these same components on the
original finite-projective and upper finite-module models.
-/
/-! Implementation source: `Quillen/Aglib/CategoryTheory/Linear/ScalarAutomorphism.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, basepoints,
coordinate order and signs are retained under native Colib ownership. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe w u v u₂ v₂ s

namespace CategoryTheory.Linear

section Scalar
variable (R : Type w) [Ring R] (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C]

/-- The canonical unit automorphism, obtained from the original category center ring map. -/
def scalarNatAut : Rˣ →* Aut (𝟭 C) :=
  (Aut.unitsEndEquivAut (𝟭 C)).toMonoidHom.comp
    (Units.map (Linear.toCatCenter R C).toMonoidHom)

/-- Every component is multiplication by the original unit on the identity morphism. -/
@[simp] theorem scalarNatAut_hom_app (r : Rˣ) (X : C) :
    (scalarNatAut R C r).asIso.hom.app X = (r : R) • 𝟙 X := rfl

/-- The inverse component uses the inverse of that same scalar unit. -/
@[simp] theorem scalarNatAut_inv_app (r : Rˣ) (X : C) :
    (scalarNatAut R C r).asIso.inv.app X = ((r⁻¹ : Rˣ) : R) • 𝟙 X := rfl

variable {C} {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear R D]

/-- An ordinary linear functor preserves the actual scalar natural-automorphism components. -/
theorem scalarNatAut_map (F : C ⥤ D) [F.Linear R] (r : Rˣ) (X : C) :
    F.map ((scalarNatAut R C r).asIso.hom.app X) =
      (scalarNatAut R D r).asIso.hom.app (F.obj X) := by
  simp only [scalarNatAut_hom_app, F.map_smul]
  exact congrArg (fun f => (r : R) • f) (F.map_id X)

end Scalar

section SmallModelAutomorphism
variable (R : Type w) [Ring R] (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C]
  [EssentiallySmall.{s} C]

/-- Lift the original scalar automorphism through the chosen model realization functor. -/
def smallModelScalarNatAut : Rˣ →* Aut (𝟭 (SmallModel.{s} C)) :=
  let F := (equivSmallModel.{s} C).inverse
  (((Functor.FullyFaithful.ofFullyFaithful F).whiskeringRight (SmallModel.{s}
    C)).autMulEquivOfFullyFaithful
     (𝟭 (SmallModel.{s} C))).symm.toMonoidHom.comp
      ((((Functor.whiskeringLeft (SmallModel.{s} C) C C).obj F).mapAut (𝟭 C)).comp
        (scalarNatAut R C))

/-- The chosen realization sends the lifted component to the original scalar identity. -/
@[simp] theorem smallModelScalarNatAut_map_hom (r : Rˣ) (X : SmallModel.{s} C) :
    (equivSmallModel.{s} C).inverse.map ((smallModelScalarNatAut R C r).asIso.hom.app X) =
      (r : R) • 𝟙 ((equivSmallModel.{s} C).inverse.obj X) := by
  let F := (equivSmallModel.{s} C).inverse
  let e := ((Functor.FullyFaithful.ofFullyFaithful F).whiskeringRight (SmallModel.{s}
    C)).autMulEquivOfFullyFaithful
     (𝟭 (SmallModel.{s} C))
  have h := e.apply_symm_apply
    ((((Functor.whiskeringLeft (SmallModel.{s} C) C C).obj F).mapAut (𝟭 C))
      (scalarNatAut R C r))
  exact (congrArg (fun a : Aut F => a.asIso.hom.app X) h).trans (scalarNatAut_hom_app R C r _)

/-- The actual chosen-model functor carries the same original scalar automorphism. -/
theorem smallModelScalarNatAut_functor_map_hom (r : Rˣ) (X : C) :
    (equivSmallModel.{s} C).functor.map ((scalarNatAut R C r).asIso.hom.app X) =
      (smallModelScalarNatAut R C r).asIso.hom.app ((equivSmallModel.{s} C).functor.obj X) := by
  let e := equivSmallModel.{s} C
  apply e.inverse.map_injective
  rw [smallModelScalarNatAut_map_hom]
  apply (cancel_epi (e.unitIso.app X).hom).mp
  have h := e.unitIso.hom.naturality ((scalarNatAut R C r).asIso.hom.app X)
  dsimp only [Functor.id_map, Functor.comp_map] at h
  exact h.symm.trans
    ((scalarNatAut R C r).asIso.hom.naturality (e.unitIso.app X).hom).symm

end SmallModelAutomorphism

end CategoryTheory.Linear
