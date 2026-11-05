/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.AlgebraicTopology.SimplicialSet.MixedOrdinalCylinder
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy


/-! # The genuine minimum-cut contraction of the mixed cylinder -/
/-! Implementation provenance: extracted from
`Quillen/Topology/Realization/MixedOrdinalContraction.lean`
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps, proofs,
assumptions, and universes are retained; only namespaces/imports are migrated.
-/
@[expose] public section

noncomputable section
open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SSet.MixedOrdinalCylinder

/-- Intersect the selected terminal segment with the interval parameter. -/
def minCut {n : SimplexCategory} (φ τ : Cut n) : Cut n :=
  SimplexCategory.Hom.mk ⟨fun i ↦ min (φ.toOrderHom i) (τ.toOrderHom i),
    φ.toOrderHom.monotone.min τ.toOrderHom.monotone⟩

@[simp] theorem comp_minCut {n m : SimplexCategory} (α : n ⟶ m) (φ τ : Cut m) :
    α ≫ minCut φ τ = minCut (α ≫ φ) (α ≫ τ) := by ext; rfl

@[simp] theorem minCut_zero {n : SimplexCategory} (φ : Cut n) : minCut φ (zeroCut n) = zeroCut n
    := by
  ext i : 3
  exact min_eq_right (Fin.zero_le _)

@[simp] theorem minCut_one {n : SimplexCategory} (φ : Cut n) : minCut φ (oneCut n) = φ := by
  ext i : 3
  exact min_eq_left (Fin.le_last _)

/-- The smaller mixed ordinal includes into the old one by its actual vertices. -/
def lowerCutMap {n : SimplexCategory} (φ τ : Cut n) : mixedOrdinal (minCut φ τ) ⟶ mixedOrdinal φ :=
  mixedMap (𝟙 n) (fun i ↦ min_le_left (φ.toOrderHom i) (τ.toOrderHom i))

@[simp] theorem lowerCutMap_naturality {n m : SimplexCategory} (α : n ⟶ m) (φ τ : Cut m) :
    mixedMap (φ := minCut (α ≫ φ) (α ≫ τ)) (ψ := minCut φ τ) α (fun _ ↦ le_rfl) ≫ lowerCutMap φ τ =
      lowerCutMap (α ≫ φ) (α ≫ τ) ≫ mixedMap α (fun _ ↦ le_rfl) := by
  simp only [lowerCutMap, mixedMap_comp, Category.comp_id, Category.id_comp]

/-- Lower the cut without changing any selected simplex data except by restriction. -/
def lowerSimplex (X : SSet.{u}) {n : SimplexCategory} (s : Simplex X n) (τ : Cut n) : Simplex X n :=
  ⟨minCut s.1 τ, X.map (lowerCutMap s.1 τ).op s.2⟩

@[simp] theorem lowerSimplex_naturality (X : SSet.{u}) {n m : SimplexCategory}
    (α : n ⟶ m) (s : Simplex X m) (τ : Cut m) :
    reindex X α (lowerSimplex X s τ) = lowerSimplex X (reindex X α s) (α ≫ τ) := by
  rcases s with ⟨φ, x⟩
  dsimp only [reindex, lowerSimplex]
  congr 1
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
  congr 2
  exact congrArg X.map (congrArg Quiver.Hom.op (lowerCutMap_naturality α φ τ))

/-- The all-zero-cut inclusion is determined by its first-copy restriction. -/
theorem mixedMap_zeroCut {n : SimplexCategory} (φ : Cut n) :
    mixedMap (φ := zeroCut n) (ψ := φ) (𝟙 n) (fun _ ↦ Fin.zero_le _) =
      zeroCollapse n ≫ firstIndex φ := by
  apply (cancel_epi (zeroIso n).inv).1
  change firstIndex (zeroCut n) ≫ _ = firstIndex (zeroCut n) ≫ _
  rw [firstIndex_naturality, Category.id_comp, ← Category.assoc,
    firstIndex_zeroCollapse, Category.id_comp]

private theorem mixedMap_source_congr {n m : SimplexCategory} {φ ψ : Cut n} {χ : Cut m}
    (e : φ = ψ) (α : n ⟶ m)
    (hφ : ∀ i, φ.toOrderHom i ≤ χ.toOrderHom (α.toOrderHom i))
    (hψ : ∀ i, ψ.toOrderHom i ≤ χ.toOrderHom (α.toOrderHom i)) :
    mixedMap α hφ = eqToHom (congrArg mixedOrdinal e) ≫ mixedMap α hψ := by
  subst ψ
  simp

private theorem simplex_eq_of_cut_eq (X : SSet.{u}) {n : SimplexCategory}
    {φ ψ χ : Cut n} (e : φ = ψ)
    (f : mixedOrdinal φ ⟶ mixedOrdinal χ) (g : mixedOrdinal ψ ⟶ mixedOrdinal χ)
    (h : f = eqToHom (congrArg mixedOrdinal e) ≫ g) (x : X.obj (op (mixedOrdinal χ))) :
    (⟨φ, X.map f.op x⟩ : Simplex X n) = ⟨ψ, X.map g.op x⟩ := by
  subst ψ
  simp only [eqToHom_refl, Category.id_comp] at h
  subst f
  rfl

@[simp] theorem lowerSimplex_zero (X : SSet.{u}) {n : SimplexCategory} (s : Simplex X n) :
    lowerSimplex X s (zeroCut n) =
      ⟨zeroCut n, X.map (zeroCollapse n).op (X.map (firstIndex s.1).op s.2)⟩ := by
  rcases s with ⟨φ, x⟩
  have h := mixedMap_source_congr (χ := φ) (minCut_zero φ) (𝟙 n)
    (fun i ↦ min_le_left (φ.toOrderHom i) ((zeroCut n).toOrderHom i))
    (fun _ ↦ Fin.zero_le _)
  rw [mixedMap_zeroCut] at h
  exact (simplex_eq_of_cut_eq X (minCut_zero φ) _ _ h x).trans (by
    simp only [op_comp, Functor.map_comp_apply])

@[simp] theorem lowerSimplex_one (X : SSet.{u}) {n : SimplexCategory} (s : Simplex X n) :
    lowerSimplex X s (oneCut n) = s := by
  rcases s with ⟨φ, x⟩
  have h := mixedMap_source_congr (χ := φ) (minCut_one φ) (𝟙 n)
    (fun i ↦ min_le_left (φ.toOrderHom i) ((oneCut n).toOrderHom i)) (fun _ ↦ le_rfl)
  rw [mixedMap_id] at h
  exact (simplex_eq_of_cut_eq X (minCut_one φ) _ _ h x).trans (by simp)

/-- The minimum-cut operation is a genuine simplicial cylinder map. -/
def contractionCylinder (X : SSet.{u}) : cylinder X ⊗ Δ[1] ⟶ cylinder X where
  app n := ↾fun z ↦ lowerSimplex X z.1 z.2.down
  naturality n m α := by
    ext z
    exact (lowerSimplex_naturality X α.unop z.1 z.2.down).symm

@[simp] theorem contractionCylinder_zero (X : SSet.{u}) :
    SSet.ι₀ ≫ contractionCylinder X = projection X ≫ zeroSection X := by
  ext n s
  exact lowerSimplex_zero X s

@[simp] theorem contractionCylinder_one (X : SSet.{u}) :
    SSet.ι₁ ≫ contractionCylinder X = 𝟙 _ := by
  ext n s
  exact lowerSimplex_one X s

/-- The mixed cylinder retracts onto its ordinary zero-cut endpoint. -/
def contraction (X : SSet.{u}) : SSet.Homotopy (projection X ≫ zeroSection X) (𝟙 _) where
  h := contractionCylinder X
  h₀ := contractionCylinder_zero X
  h₁ := contractionCylinder_one X
  rel := by ext n z; exact z.1.property.elim

end SSet.MixedOrdinalCylinder
