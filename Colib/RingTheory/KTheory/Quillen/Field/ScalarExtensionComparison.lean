/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.Quillen.Field.ScalarExtension
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeUniversal
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeExact
public import Colib.KTheory.Quillen.Map.NaturalIso

/-!
# Canonical matrix-image and tensor-extension comparison

Implementation provenance: Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd,
`Quillen/KTheory/Field/ScalarExtensionComparison.lean`.
The comparison preserves the actual semilinear unit and hence the original K-maps.
-/
@[expose] public section

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory ModuleCat
open scoped TensorProduct ChangeOfRings
attribute [local instance] Abelian.hasFiniteBiproducts

namespace FGModuleCat
variable {F L : Type u} [Field F] [Field L] (f : F →+* L)

/-- The same Hom bijection for the actual right-module base change and literal tensor extension. -/
def extensionComparisonHomEquiv
    (P : FiniteProjective.Category.{u, u} Fᵐᵒᵖ) (N : ModuleCat.{u} L) :
    (((rightProjectiveToModuleExact L).toFunctor.obj
      ((FiniteProjective.rightBaseChange f).obj P)).obj ⟶ N) ≃
    ((ModuleCat.extendScalars f).obj
      ((rightProjectiveToModuleExact F).toFunctor.obj P).obj ⟶ N) := by
  let eF := ModuleCat.restrictScalarsEquivalenceOfRingEquiv (RingEquiv.toOpposite F)
  let eL := ModuleCat.restrictScalarsEquivalenceOfRingEquiv (RingEquiv.toOpposite L)
  exact (eL.toAdjunction.homEquiv _ N).trans
    ((FiniteProjective.rightBaseChangeModuleHomEquiv f P (eL.inverse.obj N)).toEquiv.trans
      ((eF.toAdjunction.homEquiv P.obj ((ModuleCat.restrictScalars f).obj N)).symm.trans
        ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ N).symm))

section Comparison

variable (P : FiniteProjective.Category.{u, u} Fᵐᵒᵖ)

/-- The native base-change module after the actual opposite-ring restriction. -/
abbrev baseChangedModule := ((rightProjectiveToModuleExact L).toFunctor.obj
  ((FiniteProjective.rightBaseChange f).obj P)).obj
/-- The literal left tensor extension of the same original right module. -/
abbrev tensorExtendedModule := (ModuleCat.extendScalars f).obj
  ((rightProjectiveToModuleExact F).toFunctor.obj P).obj

local notation "A" => baseChangedModule f P
local notation "B" => tensorExtendedModule f P

/-- The universal comparison preserves the original semilinear base-change unit. -/
theorem extensionComparisonHomEquiv_unit (N : ModuleCat.{u} L) (h : A ⟶ N) (x : P.obj) :
    extensionComparisonHomEquiv f P N h ((1 : L) ⊗ₜ[F,f] x) =
      h (FiniteProjective.rightBaseChangeUnit f P x) := by
  change (1 : L) • h (FiniteProjective.rightBaseChangeUnit f P x) = _
  exact one_smul L _

/-- The Hom comparison is covariantly natural in its arbitrary target module. -/
theorem extensionComparisonHomEquiv_naturality
    {N N' : ModuleCat.{u} L} (h : A ⟶ N) (k : N ⟶ N') :
    extensionComparisonHomEquiv f P N' (h ≫ k) =
      extensionComparisonHomEquiv f P N h ≫ k := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  exact (extensionComparisonHomEquiv_unit f P N' (h ≫ k) x).trans
    (congrArg k (extensionComparisonHomEquiv_unit f P N h x).symm)

/-- The unique comparison between literal tensor extension and native matrix-image base change. -/
def extensionComparisonIso : B ≅ A where
  hom := extensionComparisonHomEquiv f P A (𝟙 A)
  inv := (extensionComparisonHomEquiv f P B).symm (𝟙 B)
  hom_inv_id := by
    have h := extensionComparisonHomEquiv_naturality f P (𝟙 A)
      ((extensionComparisonHomEquiv f P B).symm (𝟙 B))
    simpa only [Category.id_comp, Equiv.apply_symm_apply] using h.symm
  inv_hom_id := by
    apply (extensionComparisonHomEquiv f P A).injective
    rw [extensionComparisonHomEquiv_naturality, Equiv.apply_symm_apply, Category.id_comp]

/-- The concrete comparison sends the tensor unit to the original matrix-image unit. -/
theorem extensionComparisonIso_unit (x : P.obj) :
    (extensionComparisonIso f P).hom ((1 : L) ⊗ₜ[F,f] x) =
      FiniteProjective.rightBaseChangeUnit f P x :=
  extensionComparisonHomEquiv_unit f P A (𝟙 A) x

end Comparison

/-- Scalar extension and the actual right-to-left inclusion commute by the canonical unit. -/
def rightProjectiveExtensionIso :
    (rightProjectiveToModuleExact F).toFunctor ⋙ finiteModuleExtension f ≅
      FiniteProjective.rightBaseChange f ⋙ (rightProjectiveToModuleExact L).toFunctor :=
  NatIso.ofComponents (fun P => (ModuleCat.isFG L).isoMk (extensionComparisonIso f P))
    (by
      intro P Q g
      apply ObjectProperty.hom_ext
      apply ModuleCat.ExtendScalars.hom_ext
      intro x
      change (extensionComparisonIso f Q).hom
        ((ModuleCat.extendScalars f).map
          ((rightProjectiveToModuleExact F).toFunctor.map g).hom ((1 : L) ⊗ₜ[F,f] x)) =
        ((FiniteProjective.rightBaseChange f).map g).hom
          ((extensionComparisonIso f P).hom ((1 : L) ⊗ₜ[F,f] x))
      erw [ModuleCat.ExtendScalars.map_tmul, extensionComparisonIso_unit,
        extensionComparisonIso_unit]
      exact (DFunLike.congr_fun (FiniteProjective.rightBaseChangeUnit_naturality f g)
        x).symm)

/-- The actual original exact-functor K-maps commute with literal tensor extension. -/
theorem rightProjectiveToModuleKMap_baseChange (n : ℕ) :
    ((rightProjectiveToModuleExact L).KMap n).comp
        ((FiniteProjective.rightBaseChangeExact f).KMap n) =
      ((finiteModuleExtensionExact f).KMap n).comp
        ((rightProjectiveToModuleExact F).KMap n) := by
  rw [← ExactFunctor.KMap_comp, ← ExactFunctor.KMap_comp]
  exact ExactFunctor.KMap_eq_of_natIso (rightProjectiveExtensionIso f).symm n


end FGModuleCat
