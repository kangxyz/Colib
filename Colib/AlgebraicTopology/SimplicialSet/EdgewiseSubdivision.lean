/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.AlgebraicTopology.SimplicialSet.OrdinalJoin
public import Mathlib.AlgebraicTopology.SimplexCategory.Rev

/-! The genuine edgewise subdivision functor `[n] ↦ [n]ᵒᵖ ⋆ [n]`. -/
/-! Implementation provenance: adapted from `Quillen/Topology/Realization/Edgewise.lean`
and the pure simplicial lemmas in `EdgewiseSimplex.lean` and `EdgewiseRealization.lean`
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The genuine reversed
indexing functor, second-half endpoint, proofs, hypotheses and universes are retained.
Shared ordinal joins, diagonal, homotopy gluing and sequential invariance use their
existing native owners; no alternate realization or ordinary subdivision is substituted.
-/
@[expose] public section


noncomputable section
open CategoryTheory Opposite
open scoped Simplicial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SSet.EdgewiseSubdivision

open SSet.OrdinalJoin (joinObj joinMap left right joinMap_left joinMap_right)

/-- Edgewise subdivision's indexing endofunctor. Its first half is reversed. -/
def ε : SimplexCategory ⥤ SimplexCategory where
  obj n := joinObj n n
  map f := joinMap (SimplexCategory.rev.map f) f
  map_id n := by simp
  map_comp f g := by simp

/-- The first half is a natural inclusion from the reversal functor. -/
def first : SimplexCategory.rev ⟶ ε where
  app n := left n n
  naturality n m f := by
    change SimplexCategory.rev.map f ≫ left m m = left n n ≫ joinMap (SimplexCategory.rev.map f) f
    ext i : 3
    exact (joinMap_left (SimplexCategory.rev.map f) f i).symm


/-- The second half is a natural inclusion from the identity functor. -/
def second : 𝟭 SimplexCategory ⟶ ε where
  app n := right n n
  naturality n m f := by
    change f ≫ right m m = right n n ≫ joinMap (SimplexCategory.rev.map f) f
    ext i : 3
    exact (joinMap_right (SimplexCategory.rev.map f) f i).symm


/-- The actual edgewise subdivision of a simplicial set. -/
def subdivision (X : SSet.{u}) : SSet.{u} := ε.op ⋙ X

/-- Subdivision is functorial in the original simplicial set. -/
def subdivisionFunctor : SSet.{u} ⥤ SSet.{u} :=
  (Functor.whiskeringLeft _ _ _).obj ε.op

/-- The second-half endpoint comparison from edgewise subdivision. -/
def endpoint (X : SSet.{u}) : subdivision X ⟶ X where
  app n := X.map (second.app n.unop).op
  naturality n m f := by
    change X.map (ε.map f.unop).op ≫ X.map (second.app m.unop).op =
      X.map (second.app n.unop).op ≫ X.map f
    rw [← X.map_comp, ← X.map_comp]
    exact congrArg X.map (congrArg Quiver.Hom.op (second.naturality f.unop)).symm

/-- Endpoint comparison is natural in the simplicial set. -/
def endpointNatTrans : subdivisionFunctor.{u} ⟶ 𝟭 SSet.{u} where
  app := endpoint
  naturality X Y f := by
    ext n x
    exact (ConcreteCategory.congr_hom (f.naturality (second.app n.unop).op) x).symm

@[simp] theorem ε_map_left {p q : SimplexCategory} (f : p ⟶ q)
    (i : Fin (p.len + 1)) :
    (ε.map f).toOrderHom ((left p p).toOrderHom i) =
      (left q q).toOrderHom ((f.toOrderHom i.rev).rev) :=
  joinMap_left (SimplexCategory.rev.map f) f i

@[simp] theorem ε_map_right {p q : SimplexCategory} (f : p ⟶ q)
    (i : Fin (p.len + 1)) :
    (ε.map f).toOrderHom ((right p p).toOrderHom i) =
      (right q q).toOrderHom (f.toOrderHom i) :=
  joinMap_right (SimplexCategory.rev.map f) f i

/-- A vertex of a simplicial set determines the degenerate interval vertex
of its edgewise subdivision. -/
def vertex {X : SSet.{u}} (x : X _⦋0⦌) : (subdivision X) _⦋0⦌ := X.σ 0 x

@[simp] theorem endpoint_vertex {X : SSet.{u}} (x : X _⦋0⦌) :
    (endpoint X).app _ (vertex x) = x := by
  have hr : second.app ⦋0⦌ = SimplexCategory.δ 0 := by
    ext i : 3
    have hi : i = 0 := by
      exact @Subsingleton.elim (Fin 1) inferInstance i 0
    subst i
    rfl
  change X.map (second.app ⦋0⦌).op (X.σ 0 x) = x
  rw [hr]
  change X.δ 0 (X.σ 0 x) = x
  exact X.δ_comp_σ_self_apply 0 x

end SSet.EdgewiseSubdivision
