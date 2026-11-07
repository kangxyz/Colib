/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-!
# Finite modules on a principal closed subscheme

Restriction of scalars along the quotient map `R → R ⧸ Ideal.span {r}` is a fully faithful
additive functor on Mathlib's finite-module categories. Its essential image is exactly the
finite modules killed by `r`. Over a Noetherian ring it is exact for the standard abelian
exact structures. The ring and module universes are independent.

Modules killed by `r` are not identified with all modules killed by a power of `r`.
Such an identification on G-theory requires dévissage, not an equivalence of these categories.
No regularity, nontriviality, or properness hypothesis is imposed on `r` or its ideal.

## Implementation provenance

Adapted from lines 50–161 of
`Quillen/Aglib/Algebra/Category/FGModuleCat/PrincipalClosedSupport.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. This implementation uses Mathlib's native
`FGModuleCat`, quotient-ring action, and arbitrary-universe restriction of scalars.
The finite-module equivalence is proved directly, without a small-model replacement.
-/

@[expose] public noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory

attribute [local instance] Abelian.hasFiniteBiproducts

namespace FGModuleCat

variable {R : Type u} [CommRing R] (r : R)

/-- The coordinate ring of the principal closed subscheme defined by `r`. -/
abbrev ClosedRing := R ⧸ Ideal.span {r}

/-- Finite modules annihilated by `r`, rather than merely by a power of `r`. -/
def killedBy : ObjectProperty (FGModuleCat.{v} R) := fun M ↦ ∀ m : M, r • m = 0

/-- Actual restriction of scalars along the principal quotient map, on finite modules. -/
def closedRestriction : FGModuleCat.{v} (ClosedRing r) ⥤ FGModuleCat.{v} R :=
  (ModuleCat.isFG R).lift
    (forget₂ (FGModuleCat.{v} (ClosedRing r)) (ModuleCat.{v} (ClosedRing r)) ⋙
      ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {r}))) (fun M ↦ by
    change Module.Finite R ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {r}))).obj
      M.obj)
    let N := (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {r}))).obj M.obj
    have : Module.Finite (ClosedRing r) N := M.property
    have : IsScalarTower R (ClosedRing r) N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    exact Module.Finite.trans (ClosedRing r) N)

@[simp]
theorem closedRestriction_obj_obj (M : FGModuleCat.{v} (ClosedRing r)) :
    ((closedRestriction r).obj M).obj =
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {r}))).obj M.obj := rfl

@[simp]
theorem closedRestriction_map_hom {M N : FGModuleCat.{v} (ClosedRing r)} (g : M ⟶ N) :
    ((closedRestriction r).map g).hom =
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {r}))).map g.hom := rfl

/-- Forgetting finite generation leaves the literal native restriction-of-scalars functor. -/
theorem closedRestriction_comp_forget :
    closedRestriction.{u, v} r ⋙ forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R) =
      forget₂ (FGModuleCat.{v} (ClosedRing r)) (ModuleCat.{v} (ClosedRing r)) ⋙
        ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {r})) := rfl

/-- Every quotient-ring module is annihilated by the defining element. -/
theorem closedRestriction_killed (M : FGModuleCat.{v} (ClosedRing r)) :
    killedBy r ((closedRestriction r).obj M) := by
  intro m
  change M at m
  change (Ideal.Quotient.mk (Ideal.span {r}) r) • (m : M) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton r)), zero_smul]

/-- Restriction of scalars with codomain restricted to the actual annihilated objects. -/
def closedToKilled : FGModuleCat.{v} (ClosedRing r) ⥤ (killedBy r).FullSubcategory :=
  (killedBy r).lift (closedRestriction r) (closedRestriction_killed r)

/-- The annihilated-object factorization retains the actual restriction functor. -/
theorem closedToKilled_comp_inclusion :
    closedToKilled.{u, v} r ⋙ (killedBy r).ι = closedRestriction r := rfl

/-- Quotient-map surjectivity recovers quotient-ring linearity from `R`-linearity. -/
def fullyFaithfulClosedRestriction : (closedRestriction.{u, v} r).FullyFaithful where
  preimage {M N} g := FGModuleCat.ofHom
    { toFun := g.hom.hom
      map_add' := g.hom.hom.map_add
      map_smul' := by
        intro a m
        obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective a
        exact g.hom.hom.map_smul s m }

instance closedRestriction_full : (closedRestriction.{u, v} r).Full :=
  (fullyFaithfulClosedRestriction r).full

instance closedRestriction_faithful : (closedRestriction.{u, v} r).Faithful :=
  (fullyFaithfulClosedRestriction r).faithful

instance closedToKilled_full : (closedToKilled.{u, v} r).Full := by
  constructor
  intro M N g
  obtain ⟨h, hh⟩ := (closedRestriction r).map_surjective g.hom
  exact ⟨h, ObjectProperty.hom_ext _ hh⟩

instance closedToKilled_faithful : (closedToKilled.{u, v} r).Faithful where
  map_injective h := (closedRestriction r).map_injective (congrArg (fun k ↦ k.hom) h)

/-- Every finite annihilated `R`-module has its genuine quotient-ring module structure. -/
instance closedToKilled_essSurj : (closedToKilled.{u, v} r).EssSurj where
  mem_essImage M := by
    have hM : Module.IsTorsionBy R M.obj r := M.property
    let : Module (ClosedRing r) M.obj := hM.module
    let : IsScalarTower R (ClosedRing r) M.obj :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    let : Module.Finite (ClosedRing r) M.obj :=
      Module.Finite.of_restrictScalars_finite R (ClosedRing r) M.obj
    refine ⟨FGModuleCat.of (ClosedRing r) M.obj, ⟨?_⟩⟩
    apply ObjectProperty.isoMk
    apply ObjectProperty.isoMk
    exact (LinearEquiv.refl R M.obj).toModuleIso

instance closedToKilled_isEquivalence : (closedToKilled.{u, v} r).IsEquivalence := {}

/-- The actual quotient-ring restriction equivalence onto exactly the `r`-killed objects. -/
def closedEquivalence : FGModuleCat.{v} (ClosedRing r) ≌ (killedBy r).FullSubcategory :=
  (closedToKilled r).asEquivalence

/-- The quotient equivalence followed by the full inclusion is actual restriction of scalars. -/
theorem closedEquivalence_comp_inclusion :
    (closedEquivalence.{u, v} r).functor ⋙ (killedBy r).ι = closedRestriction r := rfl

/-- A finite module belongs to the essential image precisely when `r` kills it. -/
theorem closedRestriction_essImage_iff (M : FGModuleCat.{v} R) :
    (closedRestriction r).essImage M ↔ killedBy r M := by
  constructor
  · rintro ⟨N, ⟨e⟩⟩ m
    obtain ⟨n, rfl⟩ := (isoToLinearEquiv e).surjective m
    simpa only [map_smul, map_zero] using
      congrArg (isoToLinearEquiv e) (closedRestriction_killed r N n)
  · intro hM
    obtain ⟨N, ⟨e⟩⟩ :=
      Functor.EssSurj.mem_essImage (closedToKilled r) ⟨M, hM⟩
    exact ⟨N, ⟨(killedBy r).ι.mapIso e⟩⟩

/-- The essential-image object property is exactly annihilation by `r`. -/
theorem closedRestriction_essImage :
    (closedRestriction.{u, v} r).essImage = killedBy r := by
  funext M
  exact propext (closedRestriction_essImage_iff r M)

instance closedRestriction_additive : (closedRestriction.{u, v} r).Additive where
  map_add := by intros; apply FGModuleCat.hom_ext; rfl

instance closedToKilled_additive : (closedToKilled.{u, v} r).Additive where
  map_add := by intros; apply ObjectProperty.hom_ext; apply FGModuleCat.hom_ext; rfl

instance closedRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (closedRestriction.{u, v} r) := by
  have : PreservesFiniteColimits
      (closedRestriction r ⋙ forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)) := by
    rw [closedRestriction_comp_forget]
    exact comp_preservesFiniteColimits
      (forget₂ (FGModuleCat.{v} (ClosedRing r)) (ModuleCat.{v} (ClosedRing r)))
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {r})))
  exact preservesFiniteColimits_of_reflects_of_preserves (closedRestriction r)
    (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R))

variable [IsNoetherianRing R]

instance closedRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (closedRestriction.{u, v} r) := by
  have : PreservesFiniteLimits
      (closedRestriction r ⋙ forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)) := by
    rw [closedRestriction_comp_forget]
    exact comp_preservesFiniteLimits
      (forget₂ (FGModuleCat.{v} (ClosedRing r)) (ModuleCat.{v} (ClosedRing r)))
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {r})))
  exact preservesFiniteLimits_of_reflects_of_preserves (closedRestriction r)
    (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R))

/-- The genuine principal closed restriction is exact for the standard abelian structures. -/
def closedRestrictionExact :
    ExactFunctor (abelianExactStructure (FGModuleCat.{v} (ClosedRing r)))
      (abelianExactStructure (FGModuleCat.{v} R)) where
  toFunctor := closedRestriction r
  map_conflation _ h := h.map_of_exact _

@[simp]
theorem closedRestrictionExact_toFunctor :
    (closedRestrictionExact.{u, v} r).toFunctor = closedRestriction r := rfl

end FGModuleCat
