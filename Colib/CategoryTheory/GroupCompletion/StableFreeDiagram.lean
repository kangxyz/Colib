/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.LinearAlgebra.Matrix.RightAutomorphismsLeft
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
Implementation provenance: `Quillen/CategoryTheory/GroupCompletion/StableFreeDiagram.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# The original matrix stabilization in the projective free sequence

The matrix group maps to the actual automorphisms in the projective isomorphism
groupoid. Explicit finite basis reversal aligns matrix stabilization with the
chosen left rank-one coproduct sequence. These maps retain the actual free
objects and the original stabilization arrows.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  ModuleCat.FiniteProjective.categoryDirectSumMonoidal
  ModuleCat.FiniteProjective.directSumMonoidal

namespace ModuleCat.FiniteProjective.StableFree

variable (R : Type u) [Ring R]

/-- Actual projective automorphisms are the endomorphisms in the actual isomorphism groupoid. -/
def coreEndEquiv (n : ℕ) : Aut (free (R := Rᵐᵒᵖ) n) ≃* End (freeIso Rᵐᵒᵖ n) where
  toFun a := ⟨a⟩
  invFun a := a.iso
  map_mul' _ _ := rfl

/-- The original matrix group as actual endomorphisms of the labelled finite free object. -/
def freeEndEquiv (n : ℕ) : Matrix.GeneralLinearGroup (Fin n) R ≃* End (freeIso Rᵐᵒᵖ n) :=
  (Matrix.RightModule.leftFreeAutEquiv R n).trans (coreEndEquiv R n)

/-- A finite general linear group maps into the actual projective isomorphism groupoid. -/
def freeFunctor (n : ℕ) : SingleObj (Matrix.GeneralLinearGroup (Fin n) R) ⥤ IsoCategory Rᵐᵒᵖ :=
  SingleObj.functor (freeEndEquiv R n).toMonoidHom

/-- Left translation and the chosen free-successor isomorphism give exactly matrix stabilization. -/
lemma freeEndEquiv_step (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    freeEndEquiv R (n + 1) (StableGeneralLinear.step R n g) =
      (freeIsoSucc Rᵐᵒᵖ n).inv ≫
        (tensorLeft (freeIso Rᵐᵒᵖ 1)).map (freeEndEquiv R n g) ≫
          (freeIsoSucc Rᵐᵒᵖ n).hom := by
  apply Core.hom_ext
  change (Matrix.RightModule.leftFreeAutEquiv R (n + 1) (StableGeneralLinear.step R n g)).hom =
    (freeSuccIso (R := Rᵐᵒᵖ) n).inv ≫ (biprod.isoCoprod (free 1) (free n)).hom ≫
      coprod.map (𝟙 _) (Matrix.RightModule.leftFreeAutEquiv R n g).hom ≫
        (biprod.isoCoprod (free 1) (free n)).inv ≫ (freeSuccIso n).hom
  rw [Matrix.RightModule.leftFreeAutEquiv_step]
  simp only [Iso.trans_hom, Iso.symm_hom, biprod.mapIso_hom, Iso.refl_hom]
  congr 1
  have h : (biprod.isoCoprod (free (R := Rᵐᵒᵖ) 1) (free n)).hom ≫
      coprod.map (𝟙 _) (Matrix.RightModule.leftFreeAutEquiv R n g).hom ≫
        (biprod.isoCoprod (free 1) (free n)).inv =
      biprod.map (𝟙 _) (Matrix.RightModule.leftFreeAutEquiv R n g).hom := by
    apply biprod.hom_ext' <;> simp
  simpa only [Category.assoc] using congrArg (fun f => f ≫ (freeSuccIso n).hom) h.symm

/-- The finite group functors form an actual successor natural isomorphism for left translation. -/
def freeFunctorStepIso (n : ℕ) :
    (StableGeneralLinear.step R n).toFunctor ⋙ freeFunctor R (n + 1) ≅
      freeFunctor R n ⋙ tensorLeft (freeIso Rᵐᵒᵖ 1) :=
  NatIso.ofComponents (fun _ => (freeIsoSucc Rᵐᵒᵖ n).symm) (by
    intro X Y g
    change freeEndEquiv R (n + 1) (StableGeneralLinear.step R n g) ≫
      (freeIsoSucc Rᵐᵒᵖ n).inv =
        (freeIsoSucc Rᵐᵒᵖ n).inv ≫
          (tensorLeft (freeIso Rᵐᵒᵖ 1)).map (freeEndEquiv R n g)
    rw [freeEndEquiv_step]
    simp [Category.assoc])

/-- The matrix group as the actual endomorphism group of the chosen rank-one power. -/
def powerEndEquiv (n : ℕ) : Matrix.GeneralLinearGroup (Fin n) R ≃* End (rankOnePower Rᵐᵒᵖ n) :=
  (freeEndEquiv R n).trans (rankOnePowerIsoFree Rᵐᵒᵖ n).symm.conj

/-- Compatibility with the precise rank-one power sequence, including its chosen associators. -/
lemma powerEndEquiv_step (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    powerEndEquiv R (n + 1) (StableGeneralLinear.step R n g) =
      (tensorLeft (freeIso Rᵐᵒᵖ 1)).map (powerEndEquiv R n g) := by
  change (rankOnePowerIsoFree Rᵐᵒᵖ (n + 1)).hom ≫
      freeEndEquiv R (n + 1) (StableGeneralLinear.step R n g) ≫
        (rankOnePowerIsoFree Rᵐᵒᵖ (n + 1)).inv = _
  rw [freeEndEquiv_step]
  simp only [rankOnePowerIsoFree, Iso.trans_hom, Iso.trans_inv, Category.assoc,
    Iso.hom_inv_id_assoc]
  change (tensorLeft (freeIso Rᵐᵒᵖ 1)).map (rankOnePowerIsoFree Rᵐᵒᵖ n).hom ≫
      (tensorLeft (freeIso Rᵐᵒᵖ 1)).map (freeEndEquiv R n g) ≫
        (tensorLeft (freeIso Rᵐᵒᵖ 1)).map (rankOnePowerIsoFree Rᵐᵒᵖ n).inv = _
  simp only [← Functor.map_comp]
  rfl

/-- The original matrix group functor at the actual chosen rank-one power. -/
def powerFunctor (n : ℕ) : SingleObj (Matrix.GeneralLinearGroup (Fin n) R) ⥤ IsoCategory Rᵐᵒᵖ :=
  SingleObj.functor (powerEndEquiv R n).toMonoidHom

/-- A strict successor square from the original GL diagram to the projective free sequence. -/
lemma powerFunctor_step (n : ℕ) :
    (StableGeneralLinear.step R n).toFunctor ⋙ powerFunctor R (n + 1) =
      powerFunctor R n ⋙ tensorLeft (freeIso Rᵐᵒᵖ 1) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y g
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact powerEndEquiv_step R n g

/-- The original stable matrix system with its prescribed finite-stage transition maps. -/
def matrixGroupDiagram : ℕ ⥤ MonCat.{u} where
  obj n := MonCat.of (Matrix.GeneralLinearGroup (Fin n) R)
  map {n m} h := MonCat.ofHom (StableGeneralLinear.transition R n m (leOfHom h))
  map_id n := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro g
    exact StableGeneralLinear.transition_self R n g
  map_comp f g := by
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro a
    exact (StableGeneralLinear.transition_trans R _ _ a).symm

/-- The actual projective free telescope groups, using left direct-sum translation. -/
def powerGroupDiagram : ℕ ⥤ MonCat.{u} :=
  Functor.ofSequence (fun n => MonCat.ofHom
    ((tensorLeft (freeIso Rᵐᵒᵖ 1)).mapEnd (rankOnePower Rᵐᵒᵖ n)))

/-- The actual matrix-to-projective comparison is natural at every finite-stage arrow. -/
def matrixToPowerDiagram : matrixGroupDiagram R ⟶ powerGroupDiagram R :=
  NatTrans.ofSequence (fun n => MonCat.ofHom (powerEndEquiv R n).toMonoidHom) (by
    intro n
    apply MonCat.hom_ext
    apply MonoidHom.ext
    intro g
    change powerEndEquiv R (n + 1)
      (StableGeneralLinear.transition R n (n + 1) (Nat.le_succ n) g) = _
    rw [StableGeneralLinear.transition_succ]
    simp only [powerGroupDiagram, Functor.ofSequence_map_homOfLE_succ,
      MonCat.hom_comp, MonCat.hom_ofHom, MonoidHom.comp_apply]
    change powerEndEquiv R (n + 1) (StableGeneralLinear.step R n g) =
      (tensorLeft (freeIso Rᵐᵒᵖ 1)).map (powerEndEquiv R n g)
    exact powerEndEquiv_step R n g)


/-- The finite-rank original GL diagram and the actual projective free telescope are isomorphic. -/
def matrixPowerDiagramIso : matrixGroupDiagram R ≅ powerGroupDiagram R :=
  NatIso.ofComponents (fun n => (powerEndEquiv R n).toMonCatIso)
    (fun f => (matrixToPowerDiagram R).naturality f)

end ModuleCat.FiniteProjective.StableFree
