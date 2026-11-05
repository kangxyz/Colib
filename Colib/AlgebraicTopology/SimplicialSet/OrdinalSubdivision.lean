/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.AlgebraicTopology.SimplicialSet.OrdinalJoin


/-! # Ordinary twofold ordinal subdivision

The indexing functor is [n] ↦ [n] ⋆ [n], with neither half reversed. The
chosen endpoint is restriction to the first half, as needed by the mixed
ordinal cylinder used in additivity.
-/
/-! Implementation provenance: extracted from `Quillen/Topology/Realization/OrdinalSubdivision.lean`
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

namespace SSet.OrdinalSubdivision
open SSet.OrdinalJoin (joinObj joinMap left right joinMap_left joinMap_right)

/-- Ordinary twofold subdivision has the same map on both ordered halves. -/
def δ : SimplexCategory ⥤ SimplexCategory where
  obj n := joinObj n n
  map f := joinMap f f
  map_id n := OrdinalJoin.joinMap_id n n
  map_comp f g := OrdinalJoin.joinMap_comp f f g g

/-- Both halves, including the first, are naturally indexed by the original ordinal. -/
def first : 𝟭 SimplexCategory ⟶ δ where
  app n := left n n
  naturality n m f := by
    ext i : 3
    exact (joinMap_left f f i).symm

/-- The second-half inclusion is also natural, without reversing its order. -/
def second : 𝟭 SimplexCategory ⟶ δ where
  app n := right n n
  naturality n m f := by
    ext i : 3
    exact (joinMap_right f f i).symm

@[simp] theorem δ_map_left {p q : SimplexCategory} (f : p ⟶ q)
    (i : Fin (p.len + 1)) :
    (δ.map f).toOrderHom ((left p p).toOrderHom i) =
      (left q q).toOrderHom (f.toOrderHom i) := joinMap_left f f i

@[simp] theorem δ_map_right {p q : SimplexCategory} (f : p ⟶ q)
    (i : Fin (p.len + 1)) :
    (δ.map f).toOrderHom ((right p p).toOrderHom i) =
      (right q q).toOrderHom (f.toOrderHom i) := joinMap_right f f i

/-- The actual ordinary subdivision of a simplicial set. -/
def subdivision (X : SSet.{u}) : SSet.{u} := δ.op ⋙ X

/-- Ordinary subdivision acts by precomposition. -/
def subdivisionFunctor : SSet.{u} ⥤ SSet.{u} :=
  (Functor.whiskeringLeft _ _ _).obj δ.op

/-- The first-half endpoint comparison. -/
def endpoint (X : SSet.{u}) : subdivision X ⟶ X where
  app n := X.map (first.app n.unop).op
  naturality n m f := by
    change X.map (δ.map f.unop).op ≫ X.map (first.app m.unop).op =
      X.map (first.app n.unop).op ≫ X.map f
    rw [← X.map_comp, ← X.map_comp]
    exact congrArg X.map (congrArg Quiver.Hom.op (first.naturality f.unop)).symm

/-- First-half restriction is natural in the original simplicial set. -/
def endpointNatTrans : subdivisionFunctor.{u} ⟶ 𝟭 SSet.{u} where
  app := endpoint
  naturality X Y f := by
    ext n x
    exact (ConcreteCategory.congr_hom (f.naturality (first.app n.unop).op) x).symm

end SSet.OrdinalSubdivision
