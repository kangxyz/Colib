/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Quillen.Field.FiniteModuleRingEquivalence
public import Colib.KTheory.Quillen.Map.Functoriality
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Actual scalar extension and finite right projectives over fields

The finite-module functor is the restriction of `ModuleCat.extendScalars`.
Over fields it preserves finite limits and colimits, hence the abelian exact structures.
The right-projective inclusion uses the literal opposite-ring scalar restriction.

Implementation provenance: Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd,
`Quillen/KTheory/Field/ScalarExtensionComparison.lean` (tensor-extension portion).
-/
@[expose] public section

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped TensorProduct ChangeOfRings
attribute [local instance] Abelian.hasFiniteBiproducts

namespace FGModuleCat

variable {F L : Type u} [Field F] [Field L] (f : F →+* L)

/-- Literal tensor extension restricted to the existing finite-module categories. -/
def finiteModuleExtension : FGModuleCat.{u} F ⥤ FGModuleCat.{u} L :=
  ObjectProperty.lift _ ((ModuleCat.isFG F).ι ⋙ ModuleCat.extendScalars f)
    (fun M => by
      let := f.toAlgebra
      change Module.Finite L (L ⊗[F] M.obj)
      infer_instance)

instance finiteModuleExtension_additive : (finiteModuleExtension f).Additive where
  map_add := by
    intro X Y a b
    let := preservesBinaryBiproducts_of_preservesBinaryCoproducts (ModuleCat.extendScalars f)
    let := Functor.additive_of_preservesBinaryBiproducts (ModuleCat.extendScalars f)
    apply FGModuleCat.hom_ext
    exact congrArg ModuleCat.Hom.hom
      (Functor.map_add (ModuleCat.extendScalars f) (f := a.hom) (g := b.hom))

instance finiteModuleExtension_preservesFiniteLimits :
    PreservesFiniteLimits (finiteModuleExtension f) := by
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.Flat.of_isField (Field.toIsField F) f)
  have : PreservesFiniteLimits
      (finiteModuleExtension f ⋙ (ModuleCat.isFG L).ι) := by
    change PreservesFiniteLimits
      (forget₂ (FGModuleCat.{u} F) (ModuleCat.{u} F) ⋙ ModuleCat.extendScalars f)
    exact comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_reflects_of_preserves (finiteModuleExtension f)
    (ModuleCat.isFG L).ι

instance finiteModuleExtension_preservesFiniteColimits :
    PreservesFiniteColimits (finiteModuleExtension f) := by
  have : PreservesFiniteColimits
      (finiteModuleExtension f ⋙ (ModuleCat.isFG L).ι) := by
    change PreservesFiniteColimits
      (forget₂ (FGModuleCat.{u} F) (ModuleCat.{u} F) ⋙ ModuleCat.extendScalars f)
    exact comp_preservesFiniteColimits _ _
  exact preservesFiniteColimits_of_reflects_of_preserves (finiteModuleExtension f)
    (ModuleCat.isFG L).ι

/-- Exactness of the same literal tensor-extension functor over fields. -/
def finiteModuleExtensionExact : ExactFunctor (abelianExactStructure (FGModuleCat.{u} F))
    (abelianExactStructure (FGModuleCat.{u} L)) where
  toFunctor := finiteModuleExtension f
  map_conflation _ h := h.map_of_exact _

/-- The actual inclusion and opposite-ring scalar restriction, on the original exact categories. -/
def rightProjectiveToModuleExact (F : Type u) [Field F] :
    ExactFunctor (ModuleCat.FiniteProjective.exactStructure Fᵐᵒᵖ)
      (abelianExactStructure (FGModuleCat.{u} F)) :=
  (ModuleCat.FiniteProjective.toFiniteModuleExact Fᵐᵒᵖ).comp
    (finiteModuleRingExact (RingEquiv.toOpposite F))

/-- Right finite projectives and left finite modules have equivalent original K-groups.
The right-to-left step is restriction along the commutative-field opposite-ring equivalence. -/
def rightProjectiveModuleKEquiv (F : Type u) [Field F] (n : ℕ) :
    (ModuleCat.FiniteProjective.exactStructure.{u, u} Fᵐᵒᵖ).K n ≃*
      (abelianExactStructure (FGModuleCat.{u} F)).K n :=
  (ModuleCat.FiniteProjective.finiteModuleKEquiv Fᵐᵒᵖ n).trans
    (finiteModuleRingKEquiv (RingEquiv.toOpposite F) n)

/-- The original right-to-left comparison has precisely the composite's K-map forward. -/
@[simp] theorem rightProjectiveModuleKEquiv_apply (F : Type u) [Field F] (n : ℕ)
    (a : (ModuleCat.FiniteProjective.exactStructure.{u, u} Fᵐᵒᵖ).K n) :
    rightProjectiveModuleKEquiv F n a = (rightProjectiveToModuleExact F).KMap n a := by
  rw [rightProjectiveToModuleExact, ExactFunctor.KMap_comp]
  rfl

end FGModuleCat
