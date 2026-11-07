/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeExact
public import Colib.LinearAlgebra.Matrix.RightAutomorphisms

/-!
Implementation provenance:
`Quillen/Aglib/Algebra/Category/ModuleCat/FiniteProjectiveBaseChangeFree.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Free modules under change of rings

The image of an identity matrix is explicitly the original free right module.
The presentation equivalence yields a natural comparison between changing
coefficients in matrices and changing rings on actual projective modules.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Idempotents

namespace Matrix.RightModule

variable {R : Type u} {S : Type v} [Ring R] [Ring S]

/-- The image of the identity consists of all column vectors. -/
def identityImageEquiv (n : ℕ) :
    (linearMap (1 : Matrix (Fin n) (Fin n) R)).range ≃ₗ[Rᵐᵒᵖ] (Fin n → R) where
  toFun x := x.val
  invFun x := ⟨x, ⟨x, by simp⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Realizing an identity idempotent gives the library's chosen finite free module. -/
def freeImageIso (n : ℕ) :
    imageFunctor.obj ((toKaroubi (FreeCategory R)).obj ⟨n⟩) ≅
      ModuleCat.FiniteProjective.free (R := Rᵐᵒᵖ) n :=
  (ModuleCat.FiniteProjective.property Rᵐᵒᵖ).isoMk
    ((identityImageEquiv n).trans (columnsEquiv R n)).toModuleIso

/-- A square matrix acts on the identity summand without changing its entries. -/
def freeMatrixHom {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    (toKaroubi (FreeCategory R)).obj ⟨n⟩ ⟶ (toKaroubi (FreeCategory R)).obj ⟨n⟩ :=
  (toKaroubi (FreeCategory R)).map A

/-- The identity-image identification intertwines the original matrix unit action. -/
lemma freeImageIso_matrix_action (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) R) :
    imageFunctor.map (freeMatrixHom g.val) ≫ (freeImageIso n).hom =
      (freeImageIso n).hom ≫ (freeAutEquiv R n g).hom := by
  apply ObjectProperty.hom_ext
  have h := congrArg Iso.hom (freeAutEquiv_map R n g)
  change (freeAutEquiv R n g).hom.hom = (moduleAutEquiv R n g).hom at h
  change (imageFunctor.map (freeMatrixHom g.val)).hom ≫ (freeImageIso n).hom.hom =
    (freeImageIso n).hom.hom ≫ (freeAutEquiv R n g).hom.hom
  rw [h]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- Realization commutes naturally with entrywise change of coefficients. -/
def imageBaseChangeIso (f : R →+* S) :
    imageFunctor ⋙ ModuleCat.FiniteProjective.rightBaseChange f ≅ baseChange f ⋙ imageFunctor :=
  Functor.isoWhiskerRight imageEquivalence.unitIso.symm (baseChange f ⋙ imageFunctor)

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma baseChange_toKaroubi (f : R →+* S) (n : ℕ) :
    (baseChange f).obj ((toKaroubi (FreeCategory R)).obj ⟨n⟩) =
      (toKaroubi (FreeCategory S)).obj ⟨n⟩ := by
  refine Karoubi.ext (P := (baseChange f).obj ((toKaroubi (FreeCategory R)).obj ⟨n⟩))
    (Q := (toKaroubi (FreeCategory S)).obj ⟨n⟩) rfl ?_
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  exact Matrix.map_one f f.map_zero f.map_one

lemma baseChange_freeMatrixHom (f : R →+* S) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) :
    (baseChange f).map (freeMatrixHom A) ≫ (eqToIso (baseChange_toKaroubi f n)).hom =
      (eqToIso (baseChange_toKaroubi f n)).hom ≫ freeMatrixHom (A.map f) := by
  apply Karoubi.Hom.ext
  simp only [Karoubi.comp_f, eqToIso.hom, Karoubi.eqToHom_f]
  change ((1 : Matrix (Fin n) (Fin n) S) * (1 : Matrix (Fin n) (Fin n) R).map f) * A.map f =
    A.map f * ((1 : Matrix (Fin n) (Fin n) S) * (1 : Matrix (Fin n) (Fin n) R).map f)
  rw [Matrix.map_one f f.map_zero f.map_one]
  simp only [Matrix.one_mul, Matrix.mul_one]

/-- Actual change of rings sends the chosen rank-n free module to the chosen rank-n free module. -/
def freeBaseChangeIso (f : R →+* S) (n : ℕ) :
    (ModuleCat.FiniteProjective.rightBaseChange f).obj
        (ModuleCat.FiniteProjective.free (R := Rᵐᵒᵖ) n) ≅
      ModuleCat.FiniteProjective.free (R := Sᵐᵒᵖ) n :=
  (ModuleCat.FiniteProjective.rightBaseChange f).mapIso (freeImageIso n).symm ≪≫
    (imageBaseChangeIso f).app ((toKaroubi (FreeCategory R)).obj ⟨n⟩) ≪≫
      imageFunctor.mapIso (eqToIso (baseChange_toKaroubi f n)) ≪≫ freeImageIso n

/-- The actual free-module comparison intertwines the original general-linear-group ring map. -/
lemma freeBaseChangeIso_matrix_action (f : R →+* S) (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (ModuleCat.FiniteProjective.rightBaseChange f).map (freeAutEquiv R n g).hom ≫
        (freeBaseChangeIso f n).hom =
      (freeBaseChangeIso f n).hom ≫
        (freeAutEquiv S n (StableGeneralLinear.finiteMap f n g)).hom := by
  let F := ModuleCat.FiniteProjective.rightBaseChange f
  let eR := freeImageIso (R := R) n
  let eS := freeImageIso (R := S) n
  let P := (toKaroubi (FreeCategory R)).obj ⟨n⟩
  let a := freeMatrixHom g.val
  let c := eqToIso (baseChange_toKaroubi f n)
  have hR : (freeAutEquiv R n g).hom ≫ eR.inv = eR.inv ≫ imageFunctor.map a := by
    apply (cancel_mono eR.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [freeImageIso_matrix_action]
    simp only [eR, Iso.inv_hom_id_assoc]
  have hF : F.map (freeAutEquiv R n g).hom ≫ F.map eR.inv =
      F.map eR.inv ≫ F.map (imageFunctor.map a) := by
    rw [← F.map_comp, hR, F.map_comp]
  have hN := (imageBaseChangeIso f).hom.naturality a
  change F.map (imageFunctor.map a) ≫ ((imageBaseChangeIso f).app P).hom =
    ((imageBaseChangeIso f).app P).hom ≫ imageFunctor.map ((baseChange f).map a) at hN
  have hC := congrArg imageFunctor.map (baseChange_freeMatrixHom f g.val)
  simp only [Functor.map_comp] at hC
  change imageFunctor.map ((baseChange f).map a) ≫ imageFunctor.map c.hom =
    imageFunctor.map c.hom ≫ imageFunctor.map (freeMatrixHom (g.val.map f)) at hC
  have hS := freeImageIso_matrix_action n (StableGeneralLinear.finiteMap f n g)
  change imageFunctor.map (freeMatrixHom (g.val.map f)) ≫ eS.hom =
    eS.hom ≫ (freeAutEquiv S n (StableGeneralLinear.finiteMap f n g)).hom at hS
  change F.map (freeAutEquiv R n g).hom ≫
      (F.map eR.inv ≫ ((imageBaseChangeIso f).app P).hom ≫ imageFunctor.map c.hom ≫ eS.hom) =
    (F.map eR.inv ≫ ((imageBaseChangeIso f).app P).hom ≫ imageFunctor.map c.hom ≫ eS.hom) ≫ _
  rw [← Category.assoc, hF]
  simp only [Category.assoc]
  rw [← Category.assoc (F.map (imageFunctor.map a)), hN]
  simp only [Category.assoc]
  rw [← Category.assoc (imageFunctor.map ((baseChange f).map a)), hC]
  simp only [Category.assoc]
  rw [hS]

/-- The same actual-module square is compatible with the original stable-GL transition. -/
lemma freeBaseChangeIso_step_action (f : R →+* S) (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (ModuleCat.FiniteProjective.rightBaseChange f).map
        (freeAutEquiv R (n + 1) (StableGeneralLinear.step R n g)).hom ≫
        (freeBaseChangeIso f (n + 1)).hom =
      (freeBaseChangeIso f (n + 1)).hom ≫
        (freeAutEquiv S (n + 1)
          (StableGeneralLinear.step S n (StableGeneralLinear.finiteMap f n g))).hom := by
  simpa only [StableGeneralLinear.finiteMap_step] using
    freeBaseChangeIso_matrix_action f (n + 1) (StableGeneralLinear.step R n g)

end Matrix.RightModule
