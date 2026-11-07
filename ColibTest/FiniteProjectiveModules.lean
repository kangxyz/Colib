/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.Quillen.Field.UpperModuleComparison

/-!
# Finite-projective comparison and original forward maps

The tests keep the independent module universe over arbitrary rings and fields,
and check the right-module comparison through the opposite field.
-/

noncomputable section
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts

example (R : Type u) [Ring R]
    (S : ShortComplex (ModuleCat.FiniteProjective.Category.{u, v} R)) :
    (ModuleCat.FiniteProjective.exactStructure R).conflation S ↔ Nonempty S.Splitting :=
  ModuleCat.FiniteProjective.conflation_iff_nonempty_splitting R S

example (F : Type u) [Field F]
    (P : ModuleCat.FiniteProjective.Category.{u, v} F) :
    ((ModuleCat.FiniteProjective.toFiniteModule F).obj P).obj = P.obj := rfl

example (F : Type u) [Field F] (n : ℕ)
    (a : (ModuleCat.FiniteProjective.exactStructure.{u, v} F).K n) :
    ModuleCat.FiniteProjective.finiteModuleKEquiv F n a =
      (ModuleCat.FiniteProjective.toFiniteModuleExact F).KMap n a := rfl

example (F : Type u) [Field F] (n : ℕ)
    (a : (ModuleCat.FiniteProjective.exactStructure.{u, u} Fᵐᵒᵖ).K n) :
    FGModuleCat.rightProjectiveModuleKEquiv F n a =
      (FGModuleCat.rightProjectiveToModuleExact F).KMap n a :=
  FGModuleCat.rightProjectiveModuleKEquiv_apply F n a

example {F L : Type u} [Field F] [Field L] (f : F →+* L) :
    PreservesFiniteLimits (FGModuleCat.finiteModuleExtension f) := inferInstance

example {F L : Type u} [Field F] [Field L] (f : F →+* L) :
    PreservesFiniteColimits (FGModuleCat.finiteModuleExtension f) := inferInstance

open scoped TensorProduct ChangeOfRings
open ModuleCat.FiniteProjective

example {R : Type u} {S : Type v} [Ring R] [Ring S] (f : R →+* S)
    (P : ModuleCat.FiniteProjective.Category.{u, u} Rᵐᵒᵖ)
    (N : ModuleCat.{w} Sᵐᵒᵖ) (h : P.obj →ₛₗ[f.op] N) :
    ∃! k : ((rightBaseChange f).obj P).obj →ₗ[Sᵐᵒᵖ] N,
      k.comp (rightBaseChangeUnit f P) = h :=
  rightBaseChange_existsUnique f P N h

example {F L : Type u} [Field F] [Field L] (f : F →+* L)
    (P : ModuleCat.FiniteProjective.Category.{u, u} Fᵐᵒᵖ) (x : P.obj) :
    (FGModuleCat.extensionComparisonIso f P).hom ((1 : L) ⊗ₜ[F,f] x) =
      rightBaseChangeUnit f P x := FGModuleCat.extensionComparisonIso_unit f P x

example (F : Type u) [Field F] (n : ℕ)
    (a : (exactStructure.{u, u} Fᵐᵒᵖ).K n) :
    (abelianExactStructure (FGModuleCat.{u} F)).smallModelToOriginal.{u+1}.commonAmbientKMap n
        (FGModuleCat.rightProjectiveUpperModuleKEquiv F n a) =
      (FGModuleCat.finiteModuleRingExact (RingEquiv.toOpposite F)).KMap n
        ((toFiniteModuleExact Fᵐᵒᵖ).KMap n a) :=
  FGModuleCat.rightProjectiveUpperModuleKEquiv_toOriginal F n a

example {F L : Type u} [Field F] [Field L] (f : F →+* L) (n : ℕ) :
    (FGModuleCat.rightProjectiveUpperModuleKEquiv L n).toMonoidHom.comp
        ((rightBaseChangeExact f).KMap n) =
      ((FGModuleCat.finiteModuleExtensionExact f).smallKMap.{u+1} n).comp
        (FGModuleCat.rightProjectiveUpperModuleKEquiv F n).toMonoidHom :=
  FGModuleCat.rightProjectiveUpperModuleKEquiv_baseChange_hom f n
