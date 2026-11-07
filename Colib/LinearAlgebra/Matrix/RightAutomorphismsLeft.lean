/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.LinearAlgebra.Matrix.RightAutomorphisms
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveMonoidal

/-!
Implementation provenance: `Quillen/Aglib/LinearAlgebra/Matrix/RightAutomorphismsLeft.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Explicit left rank-one stabilization of matrix automorphisms

Reversal of the finite ordered basis converts right matrix stabilization into
left direct-sum stabilization. The basis change is explicit at every rank;
right and left direct-sum identifications are never identified definitionally.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  preservesBinaryBiproducts_of_preservesBiproducts

namespace Matrix.RightModule

variable (R : Type u) [Ring R]

/-- The explicit involution reversing the standard ordered basis. -/
def reverseColumns (n : ℕ) : (Fin n → Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] (Fin n → Rᵐᵒᵖ) where
  toFun x i := x i.rev
  invFun x i := x i.rev
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Basis reversal as an actual automorphism of the chosen finite free module. -/
def reverseIso (n : ℕ) : freeModule R n ≅ freeModule R n :=
  (reverseColumns R n).toModuleIso

/-- Matrix automorphisms in the reversed basis, adapted to left direct sums. -/
def leftModuleAutEquiv (n : ℕ) : Matrix.GeneralLinearGroup (Fin n) R ≃* Aut (freeModule R n) :=
  (moduleAutEquiv R n).trans (Aut.autMulEquivOfIso (reverseIso R n))

@[simp] lemma leftModuleAutEquiv_apply (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R)
    (x : Fin n → Rᵐᵒᵖ) (i : Fin n) :
    (leftModuleAutEquiv R n g).hom x i =
      (moduleAutEquiv R n g).hom (fun j => x j.rev) i.rev := rfl

/-- The added first coordinate is fixed after the explicit reversal. -/
lemma leftModuleAutEquiv_step_zero (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R)
    (x : Fin (n + 1) → Rᵐᵒᵖ) :
    (leftModuleAutEquiv R (n + 1) (StableGeneralLinear.step R n g)).hom x 0 = x 0 := by
  rw [leftModuleAutEquiv_apply, Fin.rev_zero, moduleAutEquiv_step_last, Fin.rev_last]

/-- All later coordinates carry the preceding reversed-basis action. -/
lemma leftModuleAutEquiv_step_succ (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R)
    (x : Fin (n + 1) → Rᵐᵒᵖ) (i : Fin n) :
    (leftModuleAutEquiv R (n + 1) (StableGeneralLinear.step R n g)).hom x i.succ =
      (leftModuleAutEquiv R n g).hom (fun j => x j.succ) i := by
  simp only [leftModuleAutEquiv_apply, Fin.rev_succ, moduleAutEquiv_step_castSucc,
    Fin.rev_castSucc]

/-- The left rank-one module isomorphism used by the projective free sequence. -/
def prependIso (n : ℕ) : freeModule R 1 ⊞ freeModule R n ≅ freeModule R (n + 1) :=
  ModuleCat.biprodIsoProd _ _ ≪≫
    ((LinearEquiv.prodCongr (LinearEquiv.funUnique (Fin 1) Rᵐᵒᵖ Rᵐᵒᵖ)
      (LinearEquiv.refl Rᵐᵒᵖ (Fin n → Rᵐᵒᵖ))).trans
        (Fin.consLinearEquiv Rᵐᵒᵖ (fun _ : Fin (n + 1) => Rᵐᵒᵖ))).toModuleIso

/-- Reversed-basis stabilization is the actual left direct-sum automorphism. -/
lemma leftModuleAutEquiv_stabilization (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (leftModuleAutEquiv R (n + 1) (StableGeneralLinear.step R n g)).hom ≫
        (prependIso R n).inv =
      (prependIso R n).inv ≫ biprod.map (𝟙 (freeModule R 1)) (leftModuleAutEquiv R n g).hom := by
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, Category.comp_id,
      prependIso, Iso.trans_inv, Category.assoc, ModuleCat.biprodIsoProd_inv_comp_fst]
    ext x
    funext i
    exact leftModuleAutEquiv_step_zero R n g x
  · simp only [Category.assoc, biprod.map_snd]
    simp only [prependIso, Iso.trans_inv, Category.assoc,
      ModuleCat.biprodIsoProd_inv_comp_snd]
    rw [← Category.assoc ((ModuleCat.biprodIsoProd (freeModule R 1) (freeModule R n)).inv),
      ModuleCat.biprodIsoProd_inv_comp_snd]
    ext x
    funext i
    exact leftModuleAutEquiv_step_succ R n g x i

/-- Equality of the complete automorphisms, with the chosen left-sum isomorphism retained. -/
lemma leftModuleAutEquiv_step (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    leftModuleAutEquiv R (n + 1) (StableGeneralLinear.step R n g) =
      (prependIso R n).symm ≪≫
        biprod.mapIso (Iso.refl (freeModule R 1)) (leftModuleAutEquiv R n g) ≪≫
          prependIso R n := by
  apply Iso.ext
  apply (cancel_mono (prependIso R n).inv).1
  simpa only [Iso.trans_hom, Iso.symm_hom, biprod.mapIso_hom, Iso.refl_hom,
    Category.assoc, Iso.hom_inv_id, Category.comp_id] using leftModuleAutEquiv_stabilization R n g

/-- The reversed matrix action in the actual finite projective category. -/
def leftFreeAutEquiv (n : ℕ) : Matrix.GeneralLinearGroup (Fin n) R ≃*
    Aut (ModuleCat.FiniteProjective.free (R := Rᵐᵒᵖ) n) :=
  let h := Functor.FullyFaithful.ofFullyFaithful (ModuleCat.FiniteProjective.property Rᵐᵒᵖ).ι
  (leftModuleAutEquiv R n).trans
    (h.autMulEquivOfFullyFaithful (ModuleCat.FiniteProjective.free (R := Rᵐᵒᵖ) n)).symm

@[simp] lemma leftFreeAutEquiv_map (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (ModuleCat.FiniteProjective.property Rᵐᵒᵖ).ι.mapIso (leftFreeAutEquiv R n g) =
      leftModuleAutEquiv R n g := by
  let h := Functor.FullyFaithful.ofFullyFaithful (ModuleCat.FiniteProjective.property Rᵐᵒᵖ).ι
  exact (h.autMulEquivOfFullyFaithful
    (ModuleCat.FiniteProjective.free (R := Rᵐᵒᵖ) n)).apply_symm_apply _

/-- The chosen projective left-sum isomorphism is precisely the module-level prepend map. -/
lemma freeSuccIso_map (n : ℕ) :
    (ModuleCat.FiniteProjective.property Rᵐᵒᵖ).ι.mapIso
        (ModuleCat.FiniteProjective.freeSuccIso (R := Rᵐᵒᵖ) n) =
      (ModuleCat.FiniteProjective.property Rᵐᵒᵖ).ι.mapBiprod
        (ModuleCat.FiniteProjective.free 1) (ModuleCat.FiniteProjective.free n) ≪≫
          prependIso R n := rfl

private lemma inclusion_biprod_naturality (n : ℕ)
    (a : End (ModuleCat.FiniteProjective.free (R := Rᵐᵒᵖ) n)) :
    (ModuleCat.FiniteProjective.property Rᵐᵒᵖ).ι.map (biprod.map (𝟙 _) a) ≫
        ((ModuleCat.FiniteProjective.property Rᵐᵒᵖ).ι.mapBiprod
          (ModuleCat.FiniteProjective.free 1) (ModuleCat.FiniteProjective.free n)).hom =
      ((ModuleCat.FiniteProjective.property Rᵐᵒᵖ).ι.mapBiprod
          (ModuleCat.FiniteProjective.free 1) (ModuleCat.FiniteProjective.free n)).hom ≫
        biprod.map (𝟙 _) ((ModuleCat.FiniteProjective.property Rᵐᵒᵖ).ι.map a) := by
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, Category.comp_id, Functor.mapBiprod_hom,
      biprod.lift_fst]
    exact congrArg (fun k : ModuleCat.FiniteProjective.free (R := Rᵐᵒᵖ) 1 ⊞
        ModuleCat.FiniteProjective.free n ⟶ ModuleCat.FiniteProjective.free 1 => k.hom)
      ((biprod.map_fst (𝟙 _) a).trans (Category.comp_id _))
  · simp only [Category.assoc, biprod.map_snd, Functor.mapBiprod_hom,
      biprod.lift_snd, biprod.lift_snd_assoc]
    exact congrArg (fun k : ModuleCat.FiniteProjective.free (R := Rᵐᵒᵖ) 1 ⊞
        ModuleCat.FiniteProjective.free n ⟶ ModuleCat.FiniteProjective.free n => k.hom)
      (biprod.map_snd (𝟙 _) a)

/-- Reversal intertwines matrix stabilization with the existing projective left-sum diagram. -/
lemma leftFreeAutEquiv_stabilization (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (leftFreeAutEquiv R (n + 1) (StableGeneralLinear.step R n g)).hom ≫
        (ModuleCat.FiniteProjective.freeSuccIso (R := Rᵐᵒᵖ) n).inv =
      (ModuleCat.FiniteProjective.freeSuccIso (R := Rᵐᵒᵖ) n).inv ≫
        biprod.map (𝟙 _) (leftFreeAutEquiv R n g).hom := by
  let F := (ModuleCat.FiniteProjective.property Rᵐᵒᵖ).ι
  apply F.map_injective
  simp only [Functor.map_comp]
  apply (cancel_mono (F.mapBiprod
    (ModuleCat.FiniteProjective.free 1) (ModuleCat.FiniteProjective.free n)).hom).1
  have hsn := congrArg Iso.inv (freeSuccIso_map R n)
  have hag := congrArg Iso.hom (leftFreeAutEquiv_map R n g)
  have has := congrArg Iso.hom
    (leftFreeAutEquiv_map R (n + 1) (StableGeneralLinear.step R n g))
  change F.map (leftFreeAutEquiv R n g).hom = (leftModuleAutEquiv R n g).hom at hag
  change F.map (leftFreeAutEquiv R (n + 1) (StableGeneralLinear.step R n g)).hom =
    (leftModuleAutEquiv R (n + 1) (StableGeneralLinear.step R n g)).hom at has
  change F.map (ModuleCat.FiniteProjective.freeSuccIso (R := Rᵐᵒᵖ) n).inv =
    (F.mapBiprod (ModuleCat.FiniteProjective.free 1) (ModuleCat.FiniteProjective.free n) ≪≫
      prependIso R n).inv at hsn
  rw [has, hsn]
  simp only [Iso.trans_inv, Category.assoc]
  rw [inclusion_biprod_naturality R n (leftFreeAutEquiv R n g).hom]
  dsimp only [F] at hag ⊢
  simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id, hag]
  exact leftModuleAutEquiv_stabilization R n g

/-- The full projective automorphism identity for the pre-existing left free sequence. -/
lemma leftFreeAutEquiv_step (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    leftFreeAutEquiv R (n + 1) (StableGeneralLinear.step R n g) =
      (ModuleCat.FiniteProjective.freeSuccIso (R := Rᵐᵒᵖ) n).symm ≪≫
        biprod.mapIso (Iso.refl _) (leftFreeAutEquiv R n g) ≪≫
          ModuleCat.FiniteProjective.freeSuccIso n := by
  apply Iso.ext
  apply (cancel_mono (ModuleCat.FiniteProjective.freeSuccIso (R := Rᵐᵒᵖ) n).inv).1
  simpa only [Iso.trans_hom, Iso.symm_hom, biprod.mapIso_hom, Iso.refl_hom,
    Category.assoc, Iso.hom_inv_id, Category.comp_id] using leftFreeAutEquiv_stabilization R n g

end Matrix.RightModule
