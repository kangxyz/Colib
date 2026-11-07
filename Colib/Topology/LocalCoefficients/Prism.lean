/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.Functoriality
public import Mathlib.AlgebraicTopology.SimplexCategory.ToMkOne
public import Mathlib.Topology.Homotopy.TopCat.ToSSet
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
/-!
Adapted from `Quillen/Topology/LocalCoefficients/Prism.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using the pinned native singular
simplices, module coproducts, and chain/homology functors.

# Singular prism simplices and their coefficient transport

A continuous homotopy produces a computable simplicial homotopy. We reuse
mathlib's combinatorial prism construction and its face identities. The first
edge of prism zero is the original homotopy track; the first edge of every
later prism is the initial endpoint map applied to the original simplex edge.
These are equalities of actual paths and coefficient morphisms, not assumptions
of homotopy invariance of homology.
-/

@[expose] public section

open Convexity

open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
namespace FundamentalGroupoid.LocalCoefficients

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  {f g : C(X, Y)}
/-- The singular simplex obtained from the original homotopy and an interval simplex. -/
def homotopySimplex (H : f.Homotopy g) {n : SimplexCategory}
    (σ : SingularSimplex X n) (t : n ⟶ ⦋1⦌) : SingularSimplex Y n where
  toFun z := H (StdSimplex.homeomorphI (StdSimplex.map t z), σ z)
  continuous_toFun := H.continuous.comp
    ((StdSimplex.homeomorphI.continuous.comp (StdSimplex.continuous_map ℝ t)).prodMk
      σ.continuous)

/-- The actual singular-set homotopy induced by a specified continuous homotopy. -/
def singularHomotopy (H : f.Homotopy g) :
    SSet.Homotopy (TopCat.toSSet.map (TopCat.ofHom f))
      (TopCat.toSSet.map (TopCat.ofHom g)) where
  h := {
    app n := ↾fun x ↦ ((TopCat.of Y).toSSetObjEquiv n).symm
      (homotopySimplex H (((TopCat.of X).toSSetObjEquiv n) x.1) (SSet.stdSimplex.objEquiv x.2))
    naturality n m α := by
      ext x
      apply ((TopCat.of Y).toSSetObjEquiv m).injective
      ext z
      change H (StdSimplex.homeomorphI (StdSimplex.map _ z), _) =
        H (StdSimplex.homeomorphI (StdSimplex.map _ (StdSimplex.map _ z)), _)
      congr 2
      exact congrArg StdSimplex.homeomorphI
        (StdSimplex.map_comp z α.unop (SSet.stdSimplex.objEquiv x.2)) }
  h₀ := by
    ext n x
    apply ((TopCat.of Y).toSSetObjEquiv n).injective
    ext z
    change H (StdSimplex.homeomorphI (StdSimplex.map (fun _ ↦ 0) z), _) = _
    simp
    rfl
  h₁ := by
    ext n x
    apply ((TopCat.of Y).toSSetObjEquiv n).injective
    ext z
    change H (StdSimplex.homeomorphI (StdSimplex.map (fun _ ↦ 1) z), _) = _
    simp
    rfl
  rel := by ext _ ⟨⟨_, ⟨⟩⟩, _⟩

/-- One of the actual simplices in the standard prism decomposition. -/
def prismSimplex (H : f.Homotopy g) {n : ℕ} (i : Fin (n + 1))
    (σ : SingularSimplex X ⦋n⦌) : SingularSimplex Y ⦋n + 1⦌ :=
  (TopCat.of Y).toSSetObjEquiv _
    (((singularHomotopy H).toSimplicialObjectHomotopy.h i)
      (((TopCat.of X).toSSetObjEquiv _).symm σ))
theorem prismSimplex_apply (H : f.Homotopy g) {n : ℕ} (i : Fin (n + 1))
    (σ : SingularSimplex X ⦋n⦌) (z : StdSimplex ℝ (Fin (n + 2))) :
    prismSimplex H i σ z =
      H (StdSimplex.homeomorphI
          (StdSimplex.map (SimplexCategory.toMk₁ i.succ.castSucc) z),
        σ (StdSimplex.map (SimplexCategory.σ i) z)) := rfl
theorem prismSimplex_first_vertex (H : f.Homotopy g) {n : ℕ}
    (i : Fin (n + 1)) (σ : SingularSimplex X ⦋n⦌) :
    prismSimplex H i σ (StdSimplex.single 0) = f (σ (StdSimplex.single 0)) := by
  rw [prismSimplex_apply]
  have ht : SimplexCategory.toMk₁ i.castSucc.succ (0 : Fin (n + 2)) = 0 :=
    SimplexCategory.toMk₁_of_castSucc_lt _ _ (by simp)
  simp [SimplexCategory.coe_σ, ht]
end FundamentalGroupoid.LocalCoefficients
namespace FundamentalGroupoid.LocalCoefficients
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  {f g : C(X, Y)}
theorem prismSimplex_face_zero (H : f.Homotopy g) {n : ℕ} (σ : SingularSimplex X ⦋n⦌) :
    restrictSimplex (prismSimplex H 0 σ) (SimplexCategory.δ 0) = g.comp σ := by
  have h := ConcreteCategory.congr_hom
    ((singularHomotopy H).toSimplicialObjectHomotopy.h_zero_comp_δ_zero n)
    (((TopCat.of X).toSSetObjEquiv _).symm σ)
  exact congrArg ((TopCat.of Y).toSSetObjEquiv _) h

theorem prismSimplex_face_last (H : f.Homotopy g) {n : ℕ} (σ : SingularSimplex X ⦋n⦌) :
    restrictSimplex (prismSimplex H (Fin.last n) σ) (SimplexCategory.δ (Fin.last (n + 1))) =
      f.comp σ := by
  have h := ConcreteCategory.congr_hom
    ((singularHomotopy H).toSimplicialObjectHomotopy.h_last_comp_δ_last n)
    (((TopCat.of X).toSSetObjEquiv _).symm σ)
  exact congrArg ((TopCat.of Y).toSSetObjEquiv _) h
end FundamentalGroupoid.LocalCoefficients
namespace FundamentalGroupoid.LocalCoefficients
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  {f g : C(X, Y)}
/-- The point at parameter `t` on the oriented edge from vertex `i` to vertex `j`. -/
def simplexEdgePoint {n : ℕ} (i j : Fin (n + 1)) (t : unitInterval) :
    StdSimplex ℝ (Fin (n + 1)) :=
  StdSimplex.map (fun k : Fin 2 ↦ if k = 0 then i else j)
    (StdSimplex.homeomorphI.symm t)
/-- The specified oriented path between two standard-simplex vertices. -/
def simplexEdgePath {n : ℕ} (i j : Fin (n + 1)) :
    Path (StdSimplex.single i : StdSimplex ℝ (Fin (n + 1))) (StdSimplex.single j) where
  toFun := simplexEdgePoint i j
  continuous_toFun := (StdSimplex.continuous_map ℝ _).comp
    StdSimplex.homeomorphI.symm.continuous
  source' := by simp [simplexEdgePoint]
  target' := by simp [simplexEdgePoint]
theorem prismSimplex_zero_first_edge (H : f.Homotopy g) {n : ℕ}
    (σ : SingularSimplex X ⦋n⦌) (t : unitInterval) :
    prismSimplex H 0 σ (simplexEdgePoint (0 : Fin (n + 2)) 1 t) =
      H (t, σ (StdSimplex.single 0)) := by
  rw [prismSimplex_apply]
  simp only [simplexEdgePoint, StdSimplex.map_map]
  have htime : (fun k : Fin 2 ↦ SimplexCategory.toMk₁
      ((0 : Fin (n + 1)).succ.castSucc) ((fun k : Fin 2 ↦ if k = 0 then 0 else 1) k)) = id := by
    funext k
    fin_cases k <;> simp [SimplexCategory.toMk₁_apply]
  have hspace : (fun k : Fin 2 ↦ (SimplexCategory.σ (0 : Fin (n + 1)))
      ((fun k : Fin 2 ↦ if k = 0 then 0 else 1) k)) = fun _ ↦ 0 := by
    funext k
    fin_cases k <;> simp [SimplexCategory.coe_σ]
  rw [htime, hspace]
  simp
end FundamentalGroupoid.LocalCoefficients
namespace FundamentalGroupoid.LocalCoefficients
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  {f g : C(X, Y)}
theorem prismSimplex_succ_first_edge (H : f.Homotopy g) {n : ℕ} (i : Fin (n + 1))
    (σ : SingularSimplex X ⦋n + 1⦌) (t : unitInterval) :
    prismSimplex H i.succ σ (simplexEdgePoint (0 : Fin (n + 3)) 1 t) =
      f (σ (simplexEdgePoint (0 : Fin (n + 2)) 1 t)) := by
  rw [prismSimplex_apply]
  simp only [simplexEdgePoint, StdSimplex.map_map]
  have htime : (fun k : Fin 2 ↦ SimplexCategory.toMk₁
      (i.succ.succ.castSucc) ((fun k : Fin 2 ↦ if k = 0 then 0 else 1) k)) = fun _ ↦ 0 := by
    funext k
    fin_cases k <;> simp [SimplexCategory.toMk₁_apply]
    simp only [Fin.lt_def, Fin.val_one, Fin.val_succ, Fin.val_castSucc]
    omega
  have hspace : (fun k : Fin 2 ↦ (SimplexCategory.σ i.succ)
      ((fun k : Fin 2 ↦ if k = 0 then 0 else 1) k)) = (fun k : Fin 2 ↦ if k = 0 then 0 else 1) := by
    funext k
    fin_cases k
    · simp [SimplexCategory.coe_σ]
    · change i.succ.predAbove 1 = (1 : Fin (n + 2))
      rw [Fin.predAbove_of_le_castSucc _ _ (by
        simp only [Fin.le_def, Fin.val_one, Fin.val_succ, Fin.val_castSucc]
        omega)]
      rfl
  rw [htime, hspace]
  simp
end FundamentalGroupoid.LocalCoefficients
namespace FundamentalGroupoid.LocalCoefficients
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  {f g : C(X, Y)}
theorem transport_congr_endpoints (A : System.{u, u} Y)
    {x y x' y' : Y} (p : Path x y) (q : Path x' y')
    (hx : x = x') (hy : y = y') (h : ∀ t, p t = q t) :
    eqToHom (congrArg (fiber A) hx) ≫ transport A q ≫
      eqToHom (congrArg (fiber A) hy.symm) = transport A p := by
  subst x' y'
  have hpq : p = q := by ext t; exact h t
  subst q
  simp

theorem prismSimplex_zero_second_vertex (H : f.Homotopy g) {n : ℕ}
    (σ : SingularSimplex X ⦋n⦌) :
    prismSimplex H 0 σ (StdSimplex.single 1) = g (σ (StdSimplex.single 0)) := by
  have h := prismSimplex_zero_first_edge H σ 1
  simpa [simplexEdgePoint] using h

theorem prismSimplex_succ_second_vertex (H : f.Homotopy g) {n : ℕ}
    (i : Fin (n + 1)) (σ : SingularSimplex X ⦋n + 1⦌) :
    prismSimplex H i.succ σ (StdSimplex.single 1) = f (σ (StdSimplex.single 1)) := by
  have h := prismSimplex_succ_first_edge H i σ 1
  simpa [simplexEdgePoint] using h

theorem prismSimplex_zero_edge_transport (H : f.Homotopy g) (A : System.{u, u} Y)
    {n : ℕ} (σ : SingularSimplex X ⦋n⦌) :
    eqToHom (congrArg (fiber A) (prismSimplex_first_vertex H 0 σ).symm) ≫
      simplexTransport A (prismSimplex H 0 σ) (StdSimplex.single 0) (StdSimplex.single 1) ≫
        eqToHom (congrArg (fiber A) (prismSimplex_zero_second_vertex H σ)) =
      transport A (H.evalAt (σ (StdSimplex.single 0))) := by
  rw [simplexTransport_eq_path A _ (simplexEdgePath 0 1)]
  apply transport_congr_endpoints A _ _
    (prismSimplex_first_vertex H 0 σ).symm (prismSimplex_zero_second_vertex H σ).symm
  intro t
  exact (prismSimplex_zero_first_edge H σ t).symm

theorem prismSimplex_succ_edge_transport (H : f.Homotopy g) (A : System.{u, u} Y)
    {n : ℕ} (i : Fin (n + 1)) (σ : SingularSimplex X ⦋n + 1⦌) :
    eqToHom (congrArg (fiber A) (prismSimplex_first_vertex H i.succ σ).symm) ≫
      simplexTransport A (prismSimplex H i.succ σ) (StdSimplex.single 0) (StdSimplex.single 1) ≫
        eqToHom (congrArg (fiber A) (prismSimplex_succ_second_vertex H i σ)) =
      simplexTransport (pullback f A) σ (StdSimplex.single 0) (StdSimplex.single 1) := by
  rw [simplexTransport_eq_path A _ (simplexEdgePath 0 1),
    simplexTransport_eq_path (pullback f A) σ (simplexEdgePath 0 1), pullback_transport]
  apply transport_congr_endpoints A _ _
    (prismSimplex_first_vertex H i.succ σ).symm
    (prismSimplex_succ_second_vertex H i σ).symm
  intro t
  exact (prismSimplex_succ_first_edge H i σ t).symm
end FundamentalGroupoid.LocalCoefficients

namespace FundamentalGroupoid.LocalCoefficients

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {f g : C(X, Y)}

theorem prismSimplex_face_of_le (H : f.Homotopy g) {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc)
    (σ : SingularSimplex X ⦋n + 1⦌) :
    restrictSimplex (prismSimplex H j.succ σ) (SimplexCategory.δ i.castSucc) =
      prismSimplex H j (restrictSimplex σ (SimplexCategory.δ i)) := by
  have h := ConcreteCategory.congr_hom
    ((singularHomotopy H).toSimplicialObjectHomotopy.h_succ_comp_δ_castSucc_of_lt i j hij)
    (((TopCat.of X).toSSetObjEquiv _).symm σ)
  exact congrArg ((TopCat.of Y).toSSetObjEquiv _) h

theorem prismSimplex_middle_face (H : f.Homotopy g) {n : ℕ}
    (j : Fin (n + 1)) (σ : SingularSimplex X ⦋n + 1⦌) :
    restrictSimplex (prismSimplex H j.succ σ) (SimplexCategory.δ j.castSucc.succ) =
      restrictSimplex (prismSimplex H j.castSucc σ) (SimplexCategory.δ j.castSucc.succ) := by
  have h := ConcreteCategory.congr_hom
    ((singularHomotopy H).toSimplicialObjectHomotopy.h_succ_comp_δ_castSucc_succ j)
    (((TopCat.of X).toSSetObjEquiv _).symm σ)
  exact congrArg ((TopCat.of Y).toSSetObjEquiv _) h

theorem prismSimplex_face_of_lt (H : f.Homotopy g) {n : ℕ}
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i)
    (σ : SingularSimplex X ⦋n + 1⦌) :
    restrictSimplex (prismSimplex H j.castSucc σ) (SimplexCategory.δ i.succ) =
      prismSimplex H j (restrictSimplex σ (SimplexCategory.δ i)) := by
  have h := ConcreteCategory.congr_hom
    ((singularHomotopy H).toSimplicialObjectHomotopy.h_castSucc_comp_δ_succ_of_lt i j hji)
    (((TopCat.of X).toSSetObjEquiv _).symm σ)
  exact congrArg ((TopCat.of Y).toSSetObjEquiv _) h

theorem prismSimplex_degeneracy_of_le (H : f.Homotopy g) {n : ℕ}
    (i j : Fin (n + 1)) (hij : i ≤ j) (σ : SingularSimplex X ⦋n⦌) :
    restrictSimplex (prismSimplex H j σ) (SimplexCategory.σ i.castSucc) =
      prismSimplex H j.succ (restrictSimplex σ (SimplexCategory.σ i)) := by
  have h := ConcreteCategory.congr_hom
    ((singularHomotopy H).toSimplicialObjectHomotopy.h_comp_σ_castSucc_of_le i j hij)
    (((TopCat.of X).toSSetObjEquiv _).symm σ)
  exact congrArg ((TopCat.of Y).toSSetObjEquiv _) h

theorem prismSimplex_degeneracy_of_ge (H : f.Homotopy g) {n : ℕ}
    (i j : Fin (n + 1)) (hji : j ≤ i) (σ : SingularSimplex X ⦋n⦌) :
    restrictSimplex (prismSimplex H j σ) (SimplexCategory.σ i.succ) =
      prismSimplex H j.castSucc (restrictSimplex σ (SimplexCategory.σ i)) := by
  have h := ConcreteCategory.congr_hom
    ((singularHomotopy H).toSimplicialObjectHomotopy.h_comp_σ_succ_of_lt i j hji)
    (((TopCat.of X).toSSetObjEquiv _).symm σ)
  exact congrArg ((TopCat.of Y).toSSetObjEquiv _) h

end FundamentalGroupoid.LocalCoefficients
