/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Quillen.SmallModel.CommonAmbientNaturality
public import Colib.KTheory.Quillen.Field.ScalarExtensionComparison

/-!
# The original upper finite-module comparison

Implementation provenance: Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd,
`Quillen/KTheory/Field/ProjectiveFiniteModules.lean`, `FiniteModuleRingEquivalence.lean`
and `ScalarExtensionComparison.lean` (upper SmallK comparison clauses).
The forward comparisons retain the actual inclusion, opposite-ring restriction,
and inverse of the original common-ambient Q-map. Their scalar-extension square
is induced by the canonical matrix-image/tensor-unit natural isomorphism.
-/
@[expose] public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts

namespace ModuleCat.FiniteProjective
variable (F : Type u) [Field F]

/-- The actual upper-universe finite-module SmallModel comparison. -/
def upperFiniteModuleKEquiv (n : ℕ) : (exactStructure.{u, u} F).K n ≃*
    (abelianExactStructure (FGModuleCat.{u} F)).SmallK.{u+1} n :=
  (finiteModuleKEquiv F n).trans
    ((abelianExactStructure (FGModuleCat.{u} F)).smallModelToOriginal.{u+1}.commonAmbientKEquiv
      n).symm

/-- The SmallModel component is the inverse of its original common-ambient Q-map. -/
theorem upperFiniteModuleKEquiv_toOriginal (n : ℕ) (a : (exactStructure.{u, u} F).K n) :
    (abelianExactStructure (FGModuleCat.{u} F)).smallModelToOriginal.{u+1}.commonAmbientKMap n
      (upperFiniteModuleKEquiv F n a) = (toFiniteModuleExact F).KMap n a := by
  let E := abelianExactStructure (FGModuleCat.{u} F)
  exact (E.smallModelToOriginal.{u+1}.commonAmbientKEquiv n).apply_symm_apply _

end ModuleCat.FiniteProjective

namespace FGModuleCat
variable {F L : Type u} [Field F] [Field L]
variable (F)

/-- Right finite projectives map to the same upper finite-module group as the client.
The opposite-ring identification is the original commutative-field scalar restriction. -/
def rightProjectiveUpperModuleKEquiv (n : ℕ) :
    (ModuleCat.FiniteProjective.exactStructure Fᵐᵒᵖ).K n ≃*
      (abelianExactStructure (FGModuleCat.{u} F)).SmallK.{u+1} n :=
  let E := abelianExactStructure (FGModuleCat.{u} F)
  (ModuleCat.FiniteProjective.finiteModuleKEquiv Fᵐᵒᵖ n).trans
    ((finiteModuleRingKEquiv (RingEquiv.toOpposite F) n).trans
      (E.smallModelToOriginal.{u+1}.commonAmbientKEquiv n).symm)

/-- Undoing the SmallModel transport exposes the two actual exact-functor K-maps. -/
theorem rightProjectiveUpperModuleKEquiv_toOriginal (n : ℕ)
    (a : (ModuleCat.FiniteProjective.exactStructure Fᵐᵒᵖ).K n) :
    (abelianExactStructure (FGModuleCat.{u} F)).smallModelToOriginal.{u+1}.commonAmbientKMap n
      (rightProjectiveUpperModuleKEquiv F n a) =
      (finiteModuleRingExact (RingEquiv.toOpposite F)).KMap n
        ((ModuleCat.FiniteProjective.toFiniteModuleExact Fᵐᵒᵖ).KMap n a) := by
  let E := abelianExactStructure (FGModuleCat.{u} F)
  exact (E.smallModelToOriginal.{u+1}.commonAmbientKEquiv n).apply_symm_apply _

variable {F} (f : F →+* L)

/-- The same actual scalar-extension square on the client's upper finite-module group. -/
theorem rightProjectiveUpperModuleKEquiv_baseChange (n : ℕ)
    (a : (ModuleCat.FiniteProjective.exactStructure Fᵐᵒᵖ).K n) :
    rightProjectiveUpperModuleKEquiv L n
        ((ModuleCat.FiniteProjective.rightBaseChangeExact f).KMap n a) =
      (finiteModuleExtensionExact f).smallKMap.{u+1} n
        (rightProjectiveUpperModuleKEquiv F n a) := by
  let EF := abelianExactStructure (FGModuleCat.{u} F)
  let EL := abelianExactStructure (FGModuleCat.{u} L)
  apply (EL.smallModelToOriginal.{u+1}.commonAmbientKEquiv n).injective
  change EL.smallModelToOriginal.{u+1}.commonAmbientKMap n
      (rightProjectiveUpperModuleKEquiv L n
        ((ModuleCat.FiniteProjective.rightBaseChangeExact f).KMap n a)) =
    EL.smallModelToOriginal.{u+1}.commonAmbientKMap n
      ((finiteModuleExtensionExact f).smallKMap.{u+1} n
        (rightProjectiveUpperModuleKEquiv F n a))
  calc
    _ = (finiteModuleRingExact (RingEquiv.toOpposite L)).KMap n
        ((ModuleCat.FiniteProjective.toFiniteModuleExact.{u, u} Lᵐᵒᵖ).KMap n
          ((ModuleCat.FiniteProjective.rightBaseChangeExact f).KMap n a)) :=
      rightProjectiveUpperModuleKEquiv_toOriginal L n _
    _ = (finiteModuleExtensionExact f).KMap n
        ((finiteModuleRingExact (RingEquiv.toOpposite F)).KMap n
          ((ModuleCat.FiniteProjective.toFiniteModuleExact.{u, u} Fᵐᵒᵖ).KMap n a)) := by
      simpa only [rightProjectiveToModuleExact, ExactFunctor.KMap_comp,
        MonoidHom.comp_apply] using
        DFunLike.congr_fun (rightProjectiveToModuleKMap_baseChange f n) a
    _ = (finiteModuleExtensionExact f).KMap n
        (EF.smallModelToOriginal.{u+1}.commonAmbientKMap n
          (rightProjectiveUpperModuleKEquiv F n a)) :=
      congrArg ((finiteModuleExtensionExact f).KMap n)
        (rightProjectiveUpperModuleKEquiv_toOriginal F n a).symm
    _ = _ := (DFunLike.congr_fun
      ((finiteModuleExtensionExact f).smallModelToOriginal_commonAmbientKMap_naturality.{u+1, u} n)
        (rightProjectiveUpperModuleKEquiv F n a)).symm

/-- Homomorphism form of scalar-extension naturality after the actual SmallModel transport. -/
theorem rightProjectiveUpperModuleKEquiv_baseChange_hom (n : ℕ) :
    (rightProjectiveUpperModuleKEquiv L n).toMonoidHom.comp
        ((ModuleCat.FiniteProjective.rightBaseChangeExact f).KMap n) =
      ((finiteModuleExtensionExact f).smallKMap.{u+1} n).comp
        (rightProjectiveUpperModuleKEquiv F n).toMonoidHom := by
  ext a
  exact rightProjectiveUpperModuleKEquiv_baseChange f n a

end FGModuleCat
