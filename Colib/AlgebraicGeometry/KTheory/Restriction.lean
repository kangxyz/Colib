/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.AlgebraicGeometry.Scheme.Restriction
public import Colib.AlgebraicGeometry.KTheory.Basic
public import Colib.KTheory.Quillen.SmallModel.Functoriality

/-!
# Native open restriction on scheme K-theory and G-theory

The homomorphisms are induced by the actual module-sheaf restriction functor,
not by chosen pullback substitutes. Their defining equalities retain this
canonical map in every degree, including degree zero. The native identity and
composition comparisons induce strict functoriality of these homomorphisms.

Implementation provenance: `Quillen/AlgebraicGeometry/Scheme/KTheory.lean` and
`Quillen/AlgebraicGeometry/Scheme/GTheory.lean` at
Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.ExactCategory

namespace AlgebraicGeometry.Scheme

/-- The canonical K-map of actual geometric open restriction. -/
def restrictK {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    K X n →* K U n :=
  (Modules.vectorBundleExactRestrict j).smallKMap n

@[simp]
theorem restrictK_eq_smallKMap {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (n : ℕ) :
    restrictK j n = (Modules.vectorBundleExactRestrict j).smallKMap n := rfl

/-- The canonical G-map of actual geometric open restriction. -/
def restrictG {U X : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian U]
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) : G X n →* G U n :=
  (Modules.coherentRestrictionExact j).smallKMap n

@[simp]
theorem restrictG_eq_smallKMap {U X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian U]
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    restrictG j n = (Modules.coherentRestrictionExact j).smallKMap n := rfl

/-- Restriction along the identity is the identity on scheme K-theory in every degree. -/
@[simp]
theorem restrictK_id (X : Scheme.{u}) (n : ℕ) :
    restrictK (𝟙 X) n = MonoidHom.id (K X n) := by
  change (Modules.vectorBundleExactRestrict (𝟙 X)).smallKMap n = _
  calc
    _ = (ExactFunctor.id (Modules.vectorBundleExactStructure X)).smallKMap n :=
      ExactFunctor.smallKMap_eq_of_natIso (Modules.vectorBundleRestrictId X) n
    _ = _ := ExactFunctor.smallKMap_id _ n

/-- Actual open restriction is contravariantly functorial on scheme K-theory. -/
@[simp]
theorem restrictK_comp {V U X : Scheme.{u}} (i : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] (n : ℕ) :
    restrictK (i ≫ j) n = (restrictK i n).comp (restrictK j n) := by
  change (Modules.vectorBundleExactRestrict (i ≫ j)).smallKMap n =
    ((Modules.vectorBundleExactRestrict i).smallKMap n).comp
      ((Modules.vectorBundleExactRestrict j).smallKMap n)
  rw [← ExactFunctor.smallKMap_comp]
  exact ExactFunctor.smallKMap_eq_of_natIso (Modules.vectorBundleRestrictComp i j) n

/-- Elementwise identity restriction on scheme K-theory. -/
@[simp]
theorem restrictK_id_apply (X : Scheme.{u}) (n : ℕ) (x : K X n) :
    restrictK (𝟙 X) n x = x :=
  DFunLike.congr_fun (restrictK_id X n) x

/-- Elementwise composition of actual open restriction on scheme K-theory. -/
theorem restrictK_comp_apply {V U X : Scheme.{u}} (i : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] (n : ℕ) (x : K X n) :
    restrictK (i ≫ j) n x = restrictK i n (restrictK j n x) :=
  DFunLike.congr_fun (restrictK_comp i j n) x

/-- Restriction along the identity is the identity on coherent G-theory in every degree. -/
@[simp]
theorem restrictG_id (X : Scheme.{u}) [IsLocallyNoetherian X] (n : ℕ) :
    restrictG (𝟙 X) n = MonoidHom.id (G X n) := by
  change (Modules.coherentRestrictionExact (𝟙 X)).smallKMap n = _
  calc
    _ = (ExactFunctor.id (Modules.coherentExactStructure X)).smallKMap n :=
      ExactFunctor.smallKMap_eq_of_natIso (Modules.coherentRestrictId X) n
    _ = _ := ExactFunctor.smallKMap_id _ n

/-- Actual open restriction is contravariantly functorial on coherent G-theory. -/
@[simp]
theorem restrictG_comp {V U X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian U] [IsLocallyNoetherian V]
    (i : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j] (n : ℕ) :
    restrictG (i ≫ j) n = (restrictG i n).comp (restrictG j n) := by
  change (Modules.coherentRestrictionExact (i ≫ j)).smallKMap n =
    ((Modules.coherentRestrictionExact i).smallKMap n).comp
      ((Modules.coherentRestrictionExact j).smallKMap n)
  rw [← ExactFunctor.smallKMap_comp]
  exact ExactFunctor.smallKMap_eq_of_natIso (Modules.coherentRestrictComp i j) n

/-- Elementwise identity restriction on coherent G-theory. -/
@[simp]
theorem restrictG_id_apply (X : Scheme.{u}) [IsLocallyNoetherian X]
    (n : ℕ) (x : G X n) : restrictG (𝟙 X) n x = x :=
  DFunLike.congr_fun (restrictG_id X n) x

/-- Elementwise composition of actual open restriction on coherent G-theory. -/
theorem restrictG_comp_apply {V U X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian U] [IsLocallyNoetherian V]
    (i : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j]
    (n : ℕ) (x : G X n) :
    restrictG (i ≫ j) n x = restrictG i n (restrictG j n x) :=
  DFunLike.congr_fun (restrictG_comp i j n) x

attribute [colib_tag "COL-0285"]
  restrictK restrictG restrictK_id restrictK_comp restrictG_id restrictG_comp

end AlgebraicGeometry.Scheme
