/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveBaseChange
public import Colib.Algebra.Category.ModuleCat.MatrixImageScalarExtension
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
Implementation provenance: Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd,
`Quillen/Aglib/Algebra/Category/ModuleCat/FiniteProjectiveBaseChangeUniversal.lean`.
The original hypotheses and maps are retained.

# The universal property of the original finite-projective change of rings

The unchanged matrix-image functor represents semilinear maps into arbitrary
modules over the target ring. The unit uses the actual presentation counit,
and every universal lift is unique. No projectivity or finiteness condition
is placed on the target module, and neither ring is assumed commutative.
This is a universal-property identification of scalar extension, not a
comparison with a separately constructed balanced tensor-product carrier.
-/
@[expose] public section
noncomputable section
open CategoryTheory Matrix
universe u v w
namespace ModuleCat.FiniteProjective
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {R : Type u} {S : Type v} [Ring R] [Ring S]

/-- The actual matrix-image presentation counit as a linear equivalence. -/
def rightBaseChangePresentationEquiv (P : Category.{u, u} Rᵐᵒᵖ) :
    (RightModule.imageFunctor.obj (RightModule.imageEquivalence.inverse.obj P)).obj ≃ₗ[Rᵐᵒᵖ]
      P.obj :=
  ((property Rᵐᵒᵖ).ι.mapIso (RightModule.imageEquivalence.counitIso.app P)).toLinearEquiv

/-- The actual semilinear scalar-extension unit, using the original presentation counit. -/
def rightBaseChangeUnit (f : R →+* S) (P : Category.{u, u} Rᵐᵒᵖ) :
    P.obj →ₛₗ[f.op] ((rightBaseChange f).obj P).obj :=
  (RightModule.imageUnit f (RightModule.imageEquivalence.inverse.obj P)).comp
    (rightBaseChangePresentationEquiv P).symm.toLinearMap

/-- The unchanged change-of-rings object has the universal Hom property against every
ambient target module, in an independent target-module universe. -/
def rightBaseChangeHomEquiv (f : R →+* S) (P : Category.{u, u} Rᵐᵒᵖ)
    (N : ModuleCat.{w} Sᵐᵒᵖ) :
    (((rightBaseChange f).obj P).obj →ₗ[Sᵐᵒᵖ] N) ≃+ (P.obj →ₛₗ[f.op] N) :=
  (RightModule.imageExtensionHomEquiv f (RightModule.imageEquivalence.inverse.obj P) N).trans
    { toFun := fun h ↦ h.comp (rightBaseChangePresentationEquiv P).symm.toLinearMap
      invFun := fun h ↦ h.comp (rightBaseChangePresentationEquiv P).toLinearMap
      left_inv := by
        intro h
        ext x
        change h ((rightBaseChangePresentationEquiv P).symm
          (rightBaseChangePresentationEquiv P x)) = h x
        rw [LinearEquiv.symm_apply_apply]
      right_inv := by
        intro h
        ext x
        change h (rightBaseChangePresentationEquiv P
          ((rightBaseChangePresentationEquiv P).symm x)) = h x
        rw [LinearEquiv.apply_symm_apply]
      map_add' := by intro h k; rfl }

/-- The representing Hom equivalence is precisely precomposition by the displayed unit. -/
theorem rightBaseChangeHomEquiv_apply (f : R →+* S) (P : Category.{u, u} Rᵐᵒᵖ)
    (N : ModuleCat.{w} Sᵐᵒᵖ) (h : ((rightBaseChange f).obj P).obj →ₗ[Sᵐᵒᵖ] N) :
    rightBaseChangeHomEquiv f P N h = h.comp (rightBaseChangeUnit f P) := by
  ext x
  rfl

/-- The genuine universal extension of a semilinear map into an arbitrary target module. -/
def rightBaseChangeLift (f : R →+* S) (P : Category.{u, u} Rᵐᵒᵖ)
    (N : ModuleCat.{w} Sᵐᵒᵖ) (h : P.obj →ₛₗ[f.op] N) :
    ((rightBaseChange f).obj P).obj →ₗ[Sᵐᵒᵖ] N :=
  (rightBaseChangeHomEquiv f P N).symm h

/-- The actual universal lift extends the specified semilinear map along the original unit. -/
@[simp] theorem rightBaseChangeLift_unit (f : R →+* S) (P : Category.{u, u} Rᵐᵒᵖ)
    (N : ModuleCat.{w} Sᵐᵒᵖ) (h : P.obj →ₛₗ[f.op] N) :
    (rightBaseChangeLift f P N h).comp (rightBaseChangeUnit f P) = h :=
  (rightBaseChangeHomEquiv f P N).apply_symm_apply h

/-- Equality after the actual unit detects equality of target-linear maps. -/
theorem rightBaseChange_hom_ext (f : R →+* S) (P : Category.{u, u} Rᵐᵒᵖ)
    (N : ModuleCat.{w} Sᵐᵒᵖ) {h k : ((rightBaseChange f).obj P).obj →ₗ[Sᵐᵒᵖ] N}
    (e : h.comp (rightBaseChangeUnit f P) = k.comp (rightBaseChangeUnit f P)) : h = k :=
  (rightBaseChangeHomEquiv f P N).injective e

/-- Every linear map with the given unit formula is the unique universal extension. -/
theorem rightBaseChangeLift_unique (f : R →+* S) (P : Category.{u, u} Rᵐᵒᵖ)
    (N : ModuleCat.{w} Sᵐᵒᵖ) (h : P.obj →ₛₗ[f.op] N)
    (k : ((rightBaseChange f).obj P).obj →ₗ[Sᵐᵒᵖ] N)
    (hk : k.comp (rightBaseChangeUnit f P) = h) :
    k = rightBaseChangeLift f P N h := by
  apply rightBaseChange_hom_ext f P N
  rw [rightBaseChangeLift_unit, hk]

/-- Every semilinear map into an arbitrary ambient target extends uniquely along the
actual scalar-extension unit of the unchanged change-of-rings object. -/
theorem rightBaseChange_existsUnique (f : R →+* S) (P : Category.{u, u} Rᵐᵒᵖ)
    (N : ModuleCat.{w} Sᵐᵒᵖ) (h : P.obj →ₛₗ[f.op] N) :
    ∃! k : ((rightBaseChange f).obj P).obj →ₗ[Sᵐᵒᵖ] N,
      k.comp (rightBaseChangeUnit f P) = h :=
  ⟨rightBaseChangeLift f P N h, rightBaseChangeLift_unit f P N h,
    fun k hk ↦ rightBaseChangeLift_unique f P N h k hk⟩

/-- Postcomposition with an arbitrary target module morphism preserves the exact Hom bijection. -/
theorem rightBaseChangeHomEquiv_naturality_target (f : R →+* S)
    (P : Category.{u, u} Rᵐᵒᵖ) {N N' : ModuleCat.{w} Sᵐᵒᵖ} (k : N ⟶ N')
    (h : ((rightBaseChange f).obj P).obj →ₗ[Sᵐᵒᵖ] N) :
    rightBaseChangeHomEquiv f P N' (k.hom.comp h) =
      k.hom.comp (rightBaseChangeHomEquiv f P N h) := by
  ext x
  rfl

/-- The displayed unit is natural for the unchanged actual change-of-rings functor. -/
theorem rightBaseChangeUnit_naturality (f : R →+* S)
    {P Q : Category.{u, u} Rᵐᵒᵖ} (g : P ⟶ Q) :
    ((rightBaseChange f).map g).hom.hom.comp (rightBaseChangeUnit f P) =
      (rightBaseChangeUnit f Q).comp g.hom.hom := by
  ext x
  change RightModule.imageMap
      ((RightModule.baseChange f).map (RightModule.imageEquivalence.inverse.map g))
      (RightModule.imageUnit f _ ((rightBaseChangePresentationEquiv P).symm x)) =
    RightModule.imageUnit f _ ((rightBaseChangePresentationEquiv Q).symm (g.hom.hom x))
  refine (RightModule.imageUnit_naturality f (RightModule.imageEquivalence.inverse.map g)
    ((rightBaseChangePresentationEquiv P).symm x)).symm.trans ?_
  apply congrArg (RightModule.imageUnit f (RightModule.imageEquivalence.inverse.obj Q))
  have he := congrArg
    (fun k : P ⟶ RightModule.imageFunctor.obj (RightModule.imageEquivalence.inverse.obj Q) ↦
      k.hom.hom x)
    (RightModule.imageEquivalence.counitIso.inv.naturality g)
  exact he.symm

/-- The Hom bijection is contravariantly natural in the original projective module. -/
theorem rightBaseChangeHomEquiv_naturality_source (f : R →+* S)
    {P Q : Category.{u, u} Rᵐᵒᵖ} (g : P ⟶ Q) (N : ModuleCat.{w} Sᵐᵒᵖ)
    (h : ((rightBaseChange f).obj Q).obj →ₗ[Sᵐᵒᵖ] N) :
    rightBaseChangeHomEquiv f P N (h.comp ((rightBaseChange f).map g).hom.hom) =
      (rightBaseChangeHomEquiv f Q N h).comp g.hom.hom := by
  rw [rightBaseChangeHomEquiv_apply, rightBaseChangeHomEquiv_apply,
    LinearMap.comp_assoc, rightBaseChangeUnit_naturality, ← LinearMap.comp_assoc]

section SameUniverse
variable {T : Type u} [Ring T]

/-- In a common carrier universe the same universal property uses the actual ambient
restriction-of-scalars functor. Its target is arbitrary, not necessarily projective. -/
def rightBaseChangeModuleHomEquiv (f : R →+* T) (P : Category.{u, u} Rᵐᵒᵖ)
    (N : ModuleCat.{u} Tᵐᵒᵖ) :
    (((rightBaseChange f).obj P).obj ⟶ N) ≃+
      (P.obj ⟶ (ModuleCat.restrictScalars f.op).obj N) :=
  ModuleCat.homAddEquiv.trans ((rightBaseChangeHomEquiv f P N).trans
    (ModuleCat.semilinearMapAddEquiv f.op P.obj N))

/-- The actual ambient Hom formulation has the same original unit formula. -/
theorem rightBaseChangeModuleHomEquiv_apply (f : R →+* T) (P : Category.{u, u} Rᵐᵒᵖ)
    (N : ModuleCat.{u} Tᵐᵒᵖ) (h : ((rightBaseChange f).obj P).obj ⟶ N) (x : P.obj) :
    rightBaseChangeModuleHomEquiv f P N h x = h (rightBaseChangeUnit f P x) := rfl

end SameUniverse
end ModuleCat.FiniteProjective
