/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.FGModuleCat.Localization.EssSurj
public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Mathlib.RingTheory.Localization.Submodule

/-!
# Actual finite-module localization at an arbitrary multiplicative set

For a commutative Noetherian ring `R` and any submonoid `S`, the literal restriction
of `ModuleCat.localizedModuleFunctor S` to `FGModuleCat` is an exact Serre localization.
Its actual kernel is the finite `S`-torsion modules. No domain, regularity or
nontriviality assumption is imposed.

## Implementation provenance

The Serre-class, denominator-clearing and localized-fullness proofs generalize
`StacksFrontier/Examples/Algebra/FGModulesModuloTorsion.lean` at Stacks commit
`f8e70c5dd04bfabcb423d5e325461f527c85a5d6`. The only field-specific step there,
its finite-basis essential-surjectivity proof, is replaced by actual finite-submodule
descent in `Localization.EssSurj`. The exact-functor packaging follows the existing
`Colib/Algebra/Category/FGModuleCat/FractionLocalization.lean` without changing it.
-/
@[expose] public noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory Module
open Stacks.Examples

attribute [local instance] Abelian.hasFiniteBiproducts

namespace FGModuleCat

/-- Finitely generated `S`-torsion modules form a Serre subcategory. -/
public instance localizationTorsionProperty_isSerreClass {R : Type u} [CommRing R]
    [IsNoetherianRing R] (S : Submonoid R) :
    (localizationTorsionProperty S : ObjectProperty (FGModuleCat.{v} R)).IsSerreClass :=
  let F := forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)
  letI : F.Additive := ⟨by intros; rfl⟩
  have hmap : ∀ (S : ShortComplex (FGModuleCat.{v} R)), S.Exact → (S.map F).Exact :=
    ((Functor.exact_tfae F).out 4 2).mp (by constructor <;> infer_instance)
  { exists_zero := by
      let Z : FGModuleCat.{v} R := FGModuleCat.of R PUnit
      refine ⟨Z, CategoryTheory.Limits.IsZero.of_full_of_faithful_of_isZero F Z ?_, ?_⟩
      · exact ModuleCat.isZero_of_subsingleton (ModuleCat.of R PUnit)
      · intro x
        exact ⟨1, by subsingleton⟩
    prop_of_mono := by
      intro X Y f hf hY x
      obtain ⟨s, hs⟩ := hY (f.hom.hom x)
      refine ⟨s, (ModuleCat.mono_iff_injective f.hom).mp (Functor.map_mono F f) ?_⟩
      simpa only [map_smul, map_zero] using hs
    prop_of_epi := by
      intro X Y f hf hX y
      obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective (F.map f)).mp
        (Functor.map_epi F f) y
      obtain ⟨s, hs⟩ := hX x
      refine ⟨s, ?_⟩
      rw [← hx]
      calc
        (s : R) • (F.map f).hom x = (F.map f).hom ((s : R) • x) := by rw [map_smul]
        _ = 0 := by simpa only [map_zero] using congrArg (F.map f).hom hs
    prop_X₂_of_shortExact := by
      intro S hS h₁ h₃ x
      let T := S.map F
      have hT : T.Exact := hmap S hS.exact
      have hTfun : Function.Exact T.f.hom T.g.hom :=
        (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).mp hT
      obtain ⟨t, ht⟩ := h₃ (S.g.hom.hom x)
      have hzero : T.g.hom ((t : R) • x) = 0 := by
        rw [map_smul]
        change (t : R) • S.g.hom.hom x = 0
        exact ht
      obtain ⟨y, hy⟩ := (hTfun ((t : R) • x)).mp hzero
      obtain ⟨s, hs⟩ := h₁ y
      refine ⟨s * t, ?_⟩
      calc
        (s * t : R) • x = (s : R) • ((t : R) • x) := by rw [mul_smul]
        _ = (s : R) • T.f.hom y := by rw [← hy]
        _ = T.f.hom ((s : R) • y) := by rw [map_smul]
        _ = 0 := by rw [hs, map_zero] }

private lemma localizedModuleFunctor_hom_lift {R : Type u} [CommRing R]
    [IsNoetherianRing R] [Small.{v, u} R] (S : Submonoid R)
    (M N : FGModuleCat.{v} R)
    (f : M.obj.localizedModule S →ₗ[Localization S]
      N.obj.localizedModule S) :
    ∃ (g : M.obj →ₗ[R] N.obj) (s : S),
      IsLocalizedModule.mapExtendScalars S
        (M.obj.localizedModuleMkLinearMap S)
        (N.obj.localizedModuleMkLinearMap S)
        (Localization S) g =
          algebraMap R (Localization S) (s : R) • f := by
  let : Module.FinitePresentation R M.obj := Module.finitePresentation_of_finite R M.obj
  let g₀ : M.obj →ₗ[R] N.obj.localizedModule S :=
    f.restrictScalars R ∘ₗ M.obj.localizedModuleMkLinearMap S
  obtain ⟨g, s, hg⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule S
    (N.obj.localizedModuleMkLinearMap S) g₀
  refine ⟨g, s, ?_⟩
  apply LinearMap.restrictScalars_injective R
  apply IsLocalizedModule.linearMap_ext S (M.obj.localizedModuleMkLinearMap S)
    (N.obj.localizedModuleMkLinearMap S)
  ext x
  calc
    (IsLocalizedModule.map S (M.obj.localizedModuleMkLinearMap S)
      (N.obj.localizedModuleMkLinearMap S)) g (M.obj.localizedModuleMkLinearMap S x) =
        N.obj.localizedModuleMkLinearMap S (g x) :=
      IsLocalizedModule.map_apply S _ _ g x
    _ = algebraMap R (Localization S) (s : R) •
      f (M.obj.localizedModuleMkLinearMap S x) := by
      simpa [g₀, LinearMap.comp_apply, LinearMap.smul_apply, Submonoid.smul_def,
        IsScalarTower.algebraMap_smul] using
        congrArg (fun q : M.obj →ₗ[R] N.obj.localizedModule S => q x) hg

/-- The actual finite-module localization is the Serre quotient by `S`-torsion. -/
public instance localizedModuleFunctor_isLocalization {R : Type u} [CommRing R]
    [IsNoetherianRing R] [Small.{v, u} R] (S : Submonoid R) :
    (localizedModuleFunctor S : FGModuleCat.{v} R ⥤
      FGModuleCat.{v} (Localization S)).IsLocalization
      (localizationTorsionProperty S : ObjectProperty (FGModuleCat.{v} R)).isoModSerre := by
  let P := localizationTorsionProperty S
  let Q := localizationTorsionModuleProperty (R := R) S
  let F := forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)
  let G := forget₂ (FGModuleCat.{v} (Localization S))
    (ModuleCat.{v} (Localization S))
  let M := ModuleCat.localizedModuleFunctor.{v} S
  let L := localizedModuleFunctor S
  let : Q.IsSerreClass := localizationTorsionModuleProperty_isSerreClass S
  let : M.IsLocalization Q.isoModSerre :=
    Stacks.Examples.localizedModuleFunctor_isLocalization S
  let : F.Additive := ⟨by intros; rfl⟩
  have hF : Limits.PreservesFiniteLimits F ∧ Limits.PreservesFiniteColimits F := by
    constructor <;> infer_instance
  let : Limits.PreservesFiniteLimits F := hF.1
  let : Limits.PreservesFiniteColimits F := hF.2
  let : Limits.PreservesFiniteLimits (F ⋙ M) := Limits.comp_preservesFiniteLimits F M
  let : Limits.PreservesFiniteColimits (F ⋙ M) := Limits.comp_preservesFiniteColimits F M
  let Φ : LocalizerMorphism P.isoModSerre Q.isoModSerre := by
    refine ⟨F, ?_⟩
    intro X Y f hf
    change P (kernel f) ∧ P (cokernel f) at hf
    exact ⟨Q.prop_of_iso (PreservesKernel.iso F f) hf.1,
      Q.prop_of_iso (PreservesCokernel.iso F f) hf.2⟩
  let : CatCommSq Φ.functor L M G := ⟨((ModuleCat.isFG (Localization S)).liftCompιIso _ _).symm⟩
  have hInv : P.isoModSerre.IsInvertedBy (F ⋙ M) := by
    intro X Y f hf
    exact Localization.inverts M Q.isoModSerre (F.map f) (Φ.map f hf)
  let H : P.isoModSerre.Localization ⥤ ModuleCat.{v} (Localization S) :=
    Localization.lift (F ⋙ M) hInv P.isoModSerre.Q
  let fac := Localization.fac (F ⋙ M) hInv P.isoModSerre.Q
  have hkernel : P = (F ⋙ M).kernel := by
    ext X
    exact (congrFun (localizedModuleFunctor_kernel_eq (R := R) S) (F.obj X)).symm.to_iff
  have hFaith : H.Faithful :=
    (ObjectProperty.SerreClassLocalization.faithful_iff P.isoModSerre.Q P H fac).2 hkernel
  have hFull : H.Full := by
    refine ⟨?_⟩
    intro X Y f
    let : P.isoModSerre.Q.EssSurj :=
      Localization.essSurj P.isoModSerre.Q P.isoModSerre
    obtain ⟨M₀, ⟨iM⟩⟩ := Functor.EssSurj.mem_essImage P.isoModSerre.Q X
    obtain ⟨N₀, ⟨iN⟩⟩ := Functor.EssSurj.mem_essImage P.isoModSerre.Q Y
    let f₀ := H.map iM.hom ≫ f ≫ H.map iN.inv
    let f₁ := (fac.app M₀).inv ≫ f₀ ≫ (fac.app N₀).hom
    obtain ⟨g, s, hg⟩ := localizedModuleFunctor_hom_lift S M₀ N₀ f₁.hom
    let g₀ : M₀ ⟶ N₀ := FGModuleCat.ofHom g
    let μ : N₀ ⟶ N₀ := FGModuleCat.ofHom ((s : R) • LinearMap.id)
    have hkerRange : Q (ModuleCat.of R (F.map μ).hom.ker) := by
      intro x
      rcases x with ⟨x, hx⟩
      refine ⟨s, ?_⟩
      apply Subtype.ext
      have hμx : (F.map μ).hom x = (s : R) • x := by
        change ((s : R) • LinearMap.id) x = (s : R) • x
        simp
      change (s : R) • x = 0
      rw [← hμx]
      exact hx
    have hker : Q (kernel (F.map μ)) :=
      Q.prop_of_iso (ModuleCat.kernelIsoKer (F.map μ)).symm hkerRange
    have hcoker : Q (cokernel (F.map μ)) := by
      intro y
      obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective
        (cokernel.π (F.map μ))).mp (by infer_instance) y
      refine ⟨s, ?_⟩
      rw [← map_smul]
      have hμx : (F.map μ).hom x = (s : R) • x := by
        change ((s : R) • LinearMap.id) x = (s : R) • x
        simp
      rw [← hμx]
      exact cokernel.condition_apply (F.map μ) x
    have hμ : P.isoModSerre μ := by
      rw [ObjectProperty.isoModSerre_iff P]
      constructor
      · rw [ObjectProperty.monoModSerre_iff P]
        have hk : Q (F.obj (kernel μ)) :=
          Q.prop_of_iso (PreservesKernel.iso F μ).symm hker
        change P (kernel μ)
        exact hk
      · rw [ObjectProperty.epiModSerre_iff P]
        have hc : Q (F.obj (cokernel μ)) :=
          Q.prop_of_iso (PreservesCokernel.iso F μ).symm hcoker
        change P (cokernel μ)
        exact hc
    have hμiso : IsIso (P.isoModSerre.Q.map μ) :=
      Localization.inverts P.isoModSerre.Q P.isoModSerre μ hμ
    let : IsIso (P.isoModSerre.Q.map μ) := hμiso
    have hFMiso : IsIso ((F ⋙ M).map μ) := hInv μ hμ
    let : IsIso ((F ⋙ M).map μ) := hFMiso
    let q₀ : P.isoModSerre.Q.obj M₀ ⟶ P.isoModSerre.Q.obj N₀ :=
      P.isoModSerre.Q.map g₀ ≫ inv (P.isoModSerre.Q.map μ)
    let q := iM.inv ≫ q₀ ≫ iN.hom
    let : Module R (M₀.obj.localizedModule S) :=
      M₀.obj.instModuleCarrierLocalizationLocalizedModule S
    let : Module R (N₀.obj.localizedModule S) :=
      N₀.obj.instModuleCarrierLocalizationLocalizedModule S
    let : Module R ((F ⋙ M).obj M₀) :=
      M₀.obj.instModuleCarrierLocalizationLocalizedModule S
    let : Module R ((F ⋙ M).obj N₀) :=
      N₀.obj.instModuleCarrierLocalizationLocalizedModule S
    let : Module (Localization S) (M₀.obj.localizedModule S) := inferInstance
    let : Module (Localization S) (N₀.obj.localizedModule S) := inferInstance
    let : Module (Localization S) ((F ⋙ M).obj M₀) := inferInstance
    let : Module (Localization S) ((F ⋙ M).obj N₀) := inferInstance
    let : IsScalarTower R (Localization S) (M₀.obj.localizedModule S) := inferInstance
    let : IsScalarTower R (Localization S) (N₀.obj.localizedModule S) := inferInstance
    let : IsScalarTower R (Localization S) ((F ⋙ M).obj M₀) := by
      change IsScalarTower R (Localization S) (M₀.obj.localizedModule S)
      infer_instance
    let : IsScalarTower R (Localization S) ((F ⋙ M).obj N₀) := by
      change IsScalarTower R (Localization S) (N₀.obj.localizedModule S)
      infer_instance
    have hmapg : ((F ⋙ M).map g₀).hom =
        algebraMap R (Localization S) (s : R) • f₁.hom := by
      change IsLocalizedModule.mapExtendScalars S
        (M₀.obj.localizedModuleMkLinearMap S) (N₀.obj.localizedModuleMkLinearMap S)
        (Localization S) g = _
      exact hg
    have hmapμ : ((F ⋙ M).map μ).hom =
        algebraMap R (Localization S) (s : R) • LinearMap.id := by
      apply LinearMap.restrictScalars_injective R
      apply IsLocalizedModule.linearMap_ext S
        (N₀.obj.localizedModuleMkLinearMap S) (N₀.obj.localizedModuleMkLinearMap S)
      ext x
      calc
        (IsLocalizedModule.map S (N₀.obj.localizedModuleMkLinearMap S)
          (N₀.obj.localizedModuleMkLinearMap S)) ((s : R) • LinearMap.id)
            (N₀.obj.localizedModuleMkLinearMap S x) =
              N₀.obj.localizedModuleMkLinearMap S ((s : R) • x) :=
          IsLocalizedModule.map_apply S _ _ ((s : R) • LinearMap.id) x
        _ = (LinearMap.restrictScalars R
            ((algebraMap R (Localization S) (s : R)) •
              (LinearMap.id : N₀.obj.localizedModule S →ₗ[Localization S]
                N₀.obj.localizedModule S)) ∘ₗ
            N₀.obj.localizedModuleMkLinearMap S) x := by
          simp
    have hfactor : (F ⋙ M).map g₀ = f₁ ≫ (F ⋙ M).map μ := by
      apply ModuleCat.hom_ext
      change ((F ⋙ M).map g₀).hom = ((F ⋙ M).map μ).hom.comp f₁.hom
      rw [hmapg, hmapμ]
      ext x
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
    have hq0 : H.map q₀ = f₀ := by
      have htr : (fac.app M₀).inv ≫ H.map q₀ ≫ (fac.app N₀).hom = f₁ := by
        dsimp [q₀]
        rw [Functor.map_comp, Functor.map_inv]
        have hnatg : (fac.app M₀).inv ≫ H.map (P.isoModSerre.Q.map g₀) =
            (F ⋙ M).map g₀ ≫ (fac.app N₀).inv :=
          (fac.inv.naturality g₀).symm
        have hnatμ0 : (F ⋙ M).map μ ≫ (fac.app N₀).inv =
            (fac.app N₀).inv ≫ H.map (P.isoModSerre.Q.map μ) :=
          fac.inv.naturality μ
        have hnatμ : inv ((F ⋙ M).map μ) ≫ (fac.app N₀).inv =
            (fac.app N₀).inv ≫ inv (H.map (P.isoModSerre.Q.map μ)) := by
          apply (cancel_mono (H.map (P.isoModSerre.Q.map μ))).1
          rw [Category.assoc, ← hnatμ0]
          simp [Category.assoc]
        calc
          (((fac.app M₀).inv ≫ H.map (P.isoModSerre.Q.map g₀)) ≫
              inv (H.map (P.isoModSerre.Q.map μ))) ≫ (fac.app N₀).hom =
            (((F ⋙ M).map g₀ ≫ (fac.app N₀).inv) ≫
              inv (H.map (P.isoModSerre.Q.map μ))) ≫ (fac.app N₀).hom := by rw [hnatg]
          _ = (F ⋙ M).map g₀ ≫
              ((fac.app N₀).inv ≫ inv (H.map (P.isoModSerre.Q.map μ)) ≫
                (fac.app N₀).hom) := by simp [Category.assoc]
          _ = (F ⋙ M).map g₀ ≫ inv ((F ⋙ M).map μ) := by
            congr 1
            calc
              (fac.app N₀).inv ≫ inv (H.map (P.isoModSerre.Q.map μ)) ≫
                (fac.app N₀).hom =
                inv ((F ⋙ M).map μ) ≫ (fac.app N₀).inv ≫ (fac.app N₀).hom := by
                  rw [← Category.assoc, ← hnatμ]
                  simp [Category.assoc]
              _ = inv ((F ⋙ M).map μ) := by simp
          _ = f₁ := by
            rw [hfactor]
            simp [Category.assoc]
      apply (cancel_epi (fac.app M₀).inv).1
      apply (cancel_mono (fac.app N₀).hom).1
      simpa [f₁, Category.assoc] using htr
    have hq : H.map q = f := by
      dsimp [q]
      rw [Functor.map_comp, Functor.map_comp]
      simp [hq0, f₀, Category.assoc]
    exact ⟨q, hq⟩
  let : H.Full := hFull
  let : H.Faithful := hFaith
  let : CatCommSq Φ.functor P.isoModSerre.Q M H := ⟨fac.symm⟩
  let : Φ.IsLocalizedFullyFaithful :=
    LocalizerMorphism.IsLocalizedFullyFaithful.mk' Φ P.isoModSerre.Q M H
      (Functor.FullyFaithful.ofFullyFaithful H)
  let : G.Full := inferInstance
  let : G.Faithful := inferInstance
  let : L.EssSurj := localizedModuleFunctor_essSurj S
  exact LocalizerMorphism.isLocalization_of_isLocalizedFullyFaithful Φ
    (iso := CatCommSq.iso Φ.functor L M G)

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Small.{v, u} R]
  (S : Submonoid R)

instance localizedModuleFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (localizedModuleFunctor.{u, v} S) :=
  ObjectProperty.SerreClassLocalization.preservesFiniteLimits _
    (localizationTorsionProperty S)

instance localizedModuleFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (localizedModuleFunctor.{u, v} S) :=
  ObjectProperty.SerreClassLocalization.preservesFiniteColimits _
    (localizationTorsionProperty S)

/-- The actual functor kernel is precisely the elementwise `S`-torsion property. -/
theorem localizedModuleFunctor_kernel :
    (localizedModuleFunctor.{u, v} S).kernel = localizationTorsionProperty S := by
  funext M
  exact propext (ObjectProperty.SerreClassLocalization.isZero_obj_iff _ _ M)

/-- The original native scalar-localization functor with its proved exactness. -/
def localizationExactFunctor :
    ExactFunctor (abelianExactStructure (FGModuleCat.{v} R))
      (abelianExactStructure (FGModuleCat.{v} (Localization S))) where
  toFunctor := localizedModuleFunctor S
  map_conflation _ hS := hS.map_of_exact _

@[simp]
theorem localizationExactFunctor_toFunctor :
    (localizationExactFunctor.{u, v} S).toFunctor = localizedModuleFunctor S := rfl

instance localizationExactFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (localizationExactFunctor.{u, v} S).toFunctor :=
  localizedModuleFunctor_preservesFiniteLimits S

instance localizationExactFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (localizationExactFunctor.{u, v} S).toFunctor :=
  localizedModuleFunctor_preservesFiniteColimits S

/-- Localization at the morphisms whose actual kernel and cokernel are killed by the functor. -/
instance localizationExactFunctor_isLocalization :
    (localizationExactFunctor.{u, v} S).toFunctor.IsLocalization
      (localizationExactFunctor S).toFunctor.kernel.isoModSerre := by
  change (localizedModuleFunctor S).IsLocalization
    (localizedModuleFunctor S).kernel.isoModSerre
  have hW : (localizedModuleFunctor.{u, v} S).kernel.isoModSerre =
      (localizationTorsionProperty S).isoModSerre := by
    ext M N f
    simp only [ObjectProperty.isoModSerre_iff, localizedModuleFunctor_kernel]
  rw [hW]
  infer_instance

end FGModuleCat
