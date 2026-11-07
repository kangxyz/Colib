/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Pullbacks
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.CyclesExact
public import Mathlib.Algebra.Homology.Double

/-! # The actual two-term identity disk functor

This uses mathlib's double complex, with the identity differential in two
consecutive degrees. The resulting actual disk functor is additive, acyclic,
termwise bounded, and exact on the inherited termwise subcategory.
-/
/-! Adapted from
`Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.IdentityDisk`
at pinned Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe v u
namespace CochainComplex

attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The actual identity disk in degrees n and n+1. -/
def identityDisk (n : ℤ) (X : A) : CochainComplex A ℤ :=
  double (𝟙 X) (show (ComplexShape.up ℤ).Rel n (n + 1) by simp)

/-- Its lower term is the original object. -/
def identityDiskIso₀ (n : ℤ) (X : A) : (identityDisk n X).X n ≅ X :=
  doubleXIso₀ _ _

/-- Its upper term is the same original object. -/
def identityDiskIso₁ (n : ℤ) (X : A) : (identityDisk n X).X (n + 1) ≅ X :=
  doubleXIso₁ _ _ (by omega)

theorem identityDisk_d (n : ℤ) (X : A) :
    (identityDisk n X).d n (n + 1) =
      (identityDiskIso₀ n X).hom ≫ (identityDiskIso₁ n X).inv := by
  simpa only [identityDisk, identityDiskIso₀, identityDiskIso₁, Category.id_comp] using
    (double_d (𝟙 X) (show (ComplexShape.up ℤ).Rel n (n + 1) by simp) (by omega))

theorem identityDisk_isZero (n : ℤ) (X : A) (i : ℤ) (h₀ : i ≠ n) (h₁ : i ≠ n + 1) :
    IsZero ((identityDisk n X).X i) :=
  isZero_double_X _ _ i h₀ h₁

/-- A morphism acts by itself in each of the two nonzero degrees. -/
def identityDiskMap (n : ℤ) {X Y : A} (f : X ⟶ Y) : identityDisk n X ⟶ identityDisk n Y :=
  mkHomFromDouble (show (ComplexShape.up ℤ).Rel n (n + 1) by simp) (by omega)
    (f ≫ (identityDiskIso₀ n Y).inv) (f ≫ (identityDiskIso₁ n Y).inv)
    (by rw [identityDisk_d]; simp)
    (by intro i hi; dsimp only [identityDisk];
        rw [double_d_eq_zero₀ _ _ _ _ (by omega), comp_zero])

@[simp]
theorem identityDiskMap_f₀ (n : ℤ) {X Y : A} (f : X ⟶ Y) :
    (identityDiskMap n f).f n =
      (identityDiskIso₀ n X).hom ≫ f ≫ (identityDiskIso₀ n Y).inv := by
  simp [identityDiskMap, identityDiskIso₀]

@[simp]
theorem identityDiskMap_f₁ (n : ℤ) {X Y : A} (f : X ⟶ Y) :
    (identityDiskMap n f).f (n + 1) =
      (identityDiskIso₁ n X).hom ≫ f ≫ (identityDiskIso₁ n Y).inv := by
  simp [identityDiskMap, identityDiskIso₁]

/-- The genuine two-term identity disk functor. -/
def identityDiskFunctor (n : ℤ) : A ⥤ CochainComplex A ℤ where
  obj := identityDisk n
  map := identityDiskMap n
  map_id X := by apply from_double_hom_ext <;> simp
  map_comp f g := by apply from_double_hom_ext <;> simp

instance identityDiskFunctor_additive (n : ℤ) : (identityDiskFunctor (A := A) n).Additive where
  map_add {X Y} f g := by
    apply from_double_hom_ext <;>
      simp [identityDiskFunctor, Preadditive.comp_add, Preadditive.add_comp]

/-- Each identity disk is actually acyclic. -/
theorem identityDisk_acyclic (n : ℤ) (X : A) : (identityDisk n X).Acyclic := by
  let K := identityDisk n X
  have hd : IsIso (K.d n (n + 1)) := by dsimp [K]; rw [identityDisk_d]; infer_instance
  intro i
  by_cases h₀ : i = n
  · subst i
    apply (K.exactAt_iff' (n - 1) n (n + 1) (by simp) (by simp)).2
    apply (ShortComplex.exact_iff_mono _ ?_).2
    · exact inferInstanceAs (Mono (K.d n (n + 1)))
    · exact (identityDisk_isZero n X (n - 1) (by omega) (by omega)).eq_of_src _ _
  · by_cases h₁ : i = n + 1
    · subst i
      apply (K.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp; omega)).2
      apply (ShortComplex.exact_iff_epi _ ?_).2
      · exact inferInstanceAs (Epi (K.d n (n + 1)))
      · exact (identityDisk_isZero n X (n + 2) (by omega) (by omega)).eq_of_tgt _ _
    · exact ExactAt.of_isZero (identityDisk_isZero n X i h₀ h₁)

/-- The lower evaluation of the actual disk functor is naturally the identity. -/
def identityDiskEvalIso₀ (n : ℤ) :
    identityDiskFunctor (A := A) n ⋙ eval A (ComplexShape.up ℤ) n ≅ 𝟭 A :=
  NatIso.ofComponents (identityDiskIso₀ n) (by
    intro X Y f
    simp [identityDiskFunctor])

/-- The upper evaluation of the actual disk functor is naturally the identity. -/
def identityDiskEvalIso₁ (n : ℤ) :
    identityDiskFunctor (A := A) n ⋙ eval A (ComplexShape.up ℤ) (n + 1) ≅ 𝟭 A :=
  NatIso.ofComponents (identityDiskIso₁ n) (by
    intro X Y f
    simp [identityDiskFunctor])

/-- The actual disk functor preserves ambient short exact sequences. -/
theorem identityDisk_shortExact (S : ShortComplex A) (hS : S.ShortExact) (n : ℤ) :
    (S.map (identityDiskFunctor n)).ShortExact := by
  apply (shortExact_iff_degreewise_shortExact _).2
  intro i
  change (S.map (identityDiskFunctor n ⋙ eval A (ComplexShape.up ℤ) i)).ShortExact
  by_cases h₀ : i = n
  · subst i
    exact (ShortComplex.shortExact_iff_of_iso (S.mapNatIso (identityDiskEvalIso₀ n))).2 hS
  · by_cases h₁ : i = n + 1
    · subst i
      exact (ShortComplex.shortExact_iff_of_iso (S.mapNatIso (identityDiskEvalIso₁ n))).2 hS
    · exact {
        mono_f := (identityDisk_isZero n S.X₁ i h₀ h₁).mono _
        epi_g := (identityDisk_isZero n S.X₃ i h₀ h₁).epi _
        exact := ShortComplex.exact_of_isZero_X₂ _ (identityDisk_isZero n S.X₂ i h₀ h₁) }

variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]

/-- Disks on objects of P are genuine bounded acyclic termwise-P complexes. -/
theorem identityDisk_mem (n : ℤ) (X : A) (hX : P X) : boundedAcyclic P (identityDisk n X) := by
  refine ⟨⟨n, n + 1, fun i hi ↦ identityDisk_isZero n X i (by omega) (by omega)⟩,
    ?_, identityDisk_acyclic n X⟩
  intro i
  by_cases h₀ : i = n
  · subst i; exact P.prop_of_iso (identityDiskIso₀ n X).symm hX
  · by_cases h₁ : i = n + 1
    · subst i; exact P.prop_of_iso (identityDiskIso₁ n X).symm hX
    · exact P.prop_of_isZero (identityDisk_isZero n X i h₀ h₁)

/-- The actual disk functor restricted to the inherited categories. -/
def boundedAcyclicDiskFunctor (n : ℤ) : P.FullSubcategory ⥤ (boundedAcyclic P).FullSubcategory :=
  (boundedAcyclic P).lift (P.ι ⋙ identityDiskFunctor n) (fun X ↦ identityDisk_mem P n X.obj
    X.property)

instance boundedAcyclicDiskFunctor_additive (n : ℤ) : (boundedAcyclicDiskFunctor P n).Additive :=
  inferInstanceAs (Functor.Additive ((boundedAcyclic P).lift _ _))

variable [(abelianExactStructure A).IsExtensionClosed P]

local instance : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P

/-- The actual two-term disk is a genuine exact functor. No kernel closure
is required for this construction. -/
def boundedAcyclicDiskExactFunctor (n : ℤ) :
    ExactFunctor (ExactSubcategory.exactStructure (abelianExactStructure A) P)
      (boundedAcyclicExactStructure P) where
  toFunctor := boundedAcyclicDiskFunctor P n
  map_conflation S hS := identityDisk_shortExact (S.map P.ι) hS n

end CochainComplex
