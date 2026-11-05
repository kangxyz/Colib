/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.AlgebraicTopology.SimplicialSet.MixedOrdinalEndpoints


/-! # The variable-suffix mixed ordinal cylinder -/
/-! Implementation provenance: extracted from
`Quillen/Topology/Realization/MixedOrdinalCylinder.lean`
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps, proofs,
assumptions, and universes are retained; only namespaces/imports are migrated.
-/
@[expose] public section

noncomputable section
open CategoryTheory Opposite
open scoped Simplicial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SSet.MixedOrdinalCylinder

/-- A mixed simplex remembers its cut and the simplex on the resulting ordinal. -/
abbrev Simplex (X : SSet.{u}) (n : SimplexCategory) :=
  Σ φ : Cut n, X.obj (op (mixedOrdinal φ))

theorem pullbackBound {n m : SimplexCategory} (α : n ⟶ m) (φ : Cut m) :
    ∀ i, (α ≫ φ).toOrderHom i ≤ φ.toOrderHom (α.toOrderHom i) := fun _ ↦ le_rfl

/-- Simplicial restriction pulls back the cut and restricts the mixed ordinal. -/
def reindex (X : SSet.{u}) {n m : SimplexCategory} (α : n ⟶ m) :
    Simplex X m → Simplex X n := fun s ↦
  ⟨α ≫ s.1, X.map (mixedMap α (pullbackBound α s.1)).op s.2⟩

@[simp] theorem reindex_id (X : SSet.{u}) (n : SimplexCategory) (s : Simplex X n) :
    reindex X (𝟙 n) s = s := by
  rcases s with ⟨φ, x⟩
  unfold Cut at φ
  change SimplexCategory.Hom n ⦋1⦌ at φ
  unfold SimplexCategory.Hom at φ
  rcases φ with ⟨f, hf⟩
  change (⟨SimplexCategory.Hom.mk ⟨f, hf⟩,
    X.map (mixedMap (φ := SimplexCategory.Hom.mk ⟨f, hf⟩)
      (ψ := SimplexCategory.Hom.mk ⟨f, hf⟩) (𝟙 n) (fun _ ↦ le_rfl)).op x⟩ : Simplex X n) = _
  rw [mixedMap_id]
  simp
  rfl

@[simp] theorem reindex_comp (X : SSet.{u}) {n m k : SimplexCategory}
    (α : n ⟶ m) (β : m ⟶ k) (s : Simplex X k) :
    reindex X α (reindex X β s) = reindex X (α ≫ β) s := by
  rcases s with ⟨φ, x⟩
  change (⟨(α ≫ β) ≫ φ, X.map (mixedMap α (pullbackBound α (β ≫ φ))).op
    (X.map (mixedMap β (pullbackBound β φ)).op x)⟩ : Simplex X n) =
      ⟨(α ≫ β) ≫ φ, X.map (mixedMap (α ≫ β) (pullbackBound (α ≫ β) φ)).op x⟩
  congr 1
  rw [← Functor.map_comp_apply, ← op_comp, mixedMap_comp]
  rfl

/-- The actual mixed ordinal cylinder, rather than an assumed cylinder space. -/
def cylinder (X : SSet.{u}) : SSet.{u} where
  obj n := Simplex X n.unop
  map α := ↾(reindex X α.unop)
  map_id n := by apply ConcreteCategory.hom_ext; intro s; exact reindex_id X n.unop s
  map_comp α β := by apply ConcreteCategory.hom_ext; intro s; exact (reindex_comp X β.unop
    α.unop s).symm

/-- Restrict a mixed simplex to its always-present first copy. -/
def projection (X : SSet.{u}) : cylinder X ⟶ X where
  app n := ↾(fun s ↦ X.map (firstIndex s.1).op s.2)
  naturality n m α := by
    ext s
    change Simplex X n.unop at s
    change X.map (firstIndex (α.unop ≫ s.1)).op
      (X.map (mixedMap α.unop (fun _ ↦ le_rfl)).op s.2) =
        X.map α (X.map (firstIndex s.1).op s.2)
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
    congr 2
    exact congrArg X.map (congrArg Quiver.Hom.op
      (firstIndex_naturality α.unop (pullbackBound α.unop s.1)))


/-- The ordinary simplices sit at the zero cut. -/
def zeroSection (X : SSet.{u}) : X ⟶ cylinder X where
  app n := ↾(fun x ↦ ⟨zeroCut n.unop, X.map (zeroCollapse n.unop).op x⟩)
  naturality n m α := by
    ext x
    change (⟨zeroCut m.unop, X.map (zeroCollapse m.unop).op (X.map α x)⟩ : Simplex X m.unop) =
      reindex X α.unop ⟨zeroCut n.unop, X.map (zeroCollapse n.unop).op x⟩
    dsimp only [reindex]
    congr 1
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
    congr 2
    exact congrArg X.map (congrArg Quiver.Hom.op (zeroCollapse_naturality α.unop).symm)

/-- The ordinary subdivision sits at the one cut. -/
def oneSection (X : SSet.{u}) : OrdinalSubdivision.subdivision X ⟶ cylinder X where
  app n := ↾(fun x ↦ ⟨oneCut n.unop, X.map (inclusion (oneCut n.unop)).op x⟩)
  naturality n m α := by
    ext x
    change X.obj (op (OrdinalSubdivision.δ.obj n.unop)) at x
    change (⟨oneCut m.unop, X.map (inclusion (oneCut m.unop)).op
      (X.map (OrdinalSubdivision.δ.map α.unop).op x)⟩ : Simplex X m.unop) =
        reindex X α.unop ⟨oneCut n.unop, X.map (inclusion (oneCut n.unop)).op x⟩
    dsimp only [reindex]
    congr 1
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
    congr 2
    exact congrArg X.map (congrArg Quiver.Hom.op
      (mixedMap_inclusion (φ := oneCut m.unop) (ψ := oneCut n.unop) α.unop (fun _ ↦ le_rfl)).symm)

@[simp] theorem zeroSection_projection (X : SSet.{u}) : zeroSection X ≫ projection X = 𝟙 X := by
  ext n x
  change X.map (firstIndex (zeroCut n.unop)).op (X.map (zeroCollapse n.unop).op x) = x
  rw [← Functor.map_comp_apply]
  simp [← op_comp]

@[simp] theorem oneSection_projection (X : SSet.{u}) :
    oneSection X ≫ projection X = OrdinalSubdivision.endpoint X := by
  ext n x
  change X.obj (op (OrdinalSubdivision.δ.obj n.unop)) at x
  change X.map (firstIndex (oneCut n.unop)).op (X.map (inclusion (oneCut n.unop)).op x) = _
  rw [← Functor.map_comp_apply]
  simp only [← op_comp, firstIndex_inclusion]
  rfl

end SSet.MixedOrdinalCylinder
