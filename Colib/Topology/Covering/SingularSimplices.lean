/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.Chains
public import Colib.Topology.Realization.SimplexConnectivity
public import Mathlib.Topology.Homotopy.Lifting

/-!
Extracted from `Quillen/Topology/Covering/SingularSimplices.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Independent source and target
universes, actual covering monodromy, and all simplex restrictions are retained.
The parameter space is the pinned native function-subtype `stdSimplex`, with its
original vertices and simplicial maps, instead of newer convex-space coordinates.

# Singular simplices in a supplied covering space

For an actual covering map, a singular simplex in the total space is precisely
a singular simplex in the base together with a lift of its first vertex.
The inverse is the unique continuous simplex lift. Restriction along every
simplicial operator transports the chosen point by actual covering monodromy
from the original first vertex to the new first vertex. In particular, the
zeroth face uses the edge from vertex zero to vertex one.

The total and base spaces have independent universes. No universal-cover
existence, CW hypothesis, or homological Whitehead theorem is assumed or proved.
-/

@[expose] public section

open FundamentalGroupoid.LocalCoefficients


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory
open scoped Simplicial

universe u v u' v'

namespace IsCoveringMap

open FundamentalGroupoid.LocalCoefficients

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
variable {p : E → B} (hp : IsCoveringMap p)

/-- The original covering projection, as a continuous map. -/
def projection : C(E, B) := ⟨p, hp.continuous⟩

/-- A base singular simplex with a chosen point over its first vertex. -/
abbrev BasedSimplex (p : E → B) (n : SimplexCategory) :=
  Σ σ : SingularSimplex B n, {e : E // p e = σ (stdSimplex.vertex 0)}

/-- Existence and uniqueness of an actual continuous simplex lift. -/
theorem existsUnique_lift (hp : IsCoveringMap p) {n : SimplexCategory} (σ : SingularSimplex B n)
    (e : E) (he : p e = σ (stdSimplex.vertex 0)) :
    ∃! τ : SingularSimplex E n,
      τ (stdSimplex.vertex 0) = e ∧ p ∘ τ = σ := by
  let := stdSimplex.simplyConnectedSpace (Fin (n.len + 1))
  let := stdSimplex.locallyPathConnectedSpace (Fin (n.len + 1))
  exact hp.existsUnique_continuousMap_lifts σ (stdSimplex.vertex 0) e he

/-- The unique lift with the specified first vertex. -/
def lift {n : SimplexCategory} (σ : SingularSimplex B n)
    (e : E) (he : p e = σ (stdSimplex.vertex 0)) : SingularSimplex E n :=
  (existsUnique_lift hp σ e he).exists.choose

@[simp]
theorem lift_vertex {n : SimplexCategory} (σ : SingularSimplex B n)
    (e : E) (he : p e = σ (stdSimplex.vertex 0)) :
    lift hp σ e he (stdSimplex.vertex 0) = e :=
  (existsUnique_lift hp σ e he).exists.choose_spec.1

@[simp]
theorem projection_lift {n : SimplexCategory} (σ : SingularSimplex B n)
    (e : E) (he : p e = σ (stdSimplex.vertex 0)) :
    (projection hp).comp (lift hp σ e he) = σ := by
  ext x
  exact congr_fun (existsUnique_lift hp σ e he).exists.choose_spec.2 x

/-- A lift is determined by its projection and first vertex. -/
theorem eq_lift {n : SimplexCategory} (σ : SingularSimplex B n)
    (e : E) (he : p e = σ (stdSimplex.vertex 0)) (τ : SingularSimplex E n)
    (hτ : (projection hp).comp τ = σ) (hτ₀ : τ (stdSimplex.vertex 0) = e) :
    τ = lift hp σ e he := by
  apply (existsUnique_lift hp σ e he).unique
  · exact ⟨hτ₀, congrArg (fun f : C(_, B) ↦ (f : _ → B)) hτ⟩
  · exact (existsUnique_lift hp σ e he).exists.choose_spec

/-- The forward map is literally projection and evaluation at the first vertex. -/
def simplexEquiv (n : SimplexCategory) : SingularSimplex E n ≃ BasedSimplex p n where
  toFun τ := ⟨(projection hp).comp τ, ⟨τ (stdSimplex.vertex 0), rfl⟩⟩
  invFun s := lift hp s.1 s.2.1 s.2.2
  left_inv τ := (eq_lift hp _ _ rfl τ rfl rfl).symm
  right_inv s := by
    rcases s with ⟨σ, e, he⟩
    apply Sigma.ext (projection_lift hp σ e he)
    apply (Subtype.heq_iff_coe_eq (fun x ↦ by
      change p x = ((projection hp).comp (lift hp σ e he)) (stdSimplex.vertex 0) ↔
        p x = σ (stdSimplex.vertex 0)
      rw [projection_lift])).mpr
    exact lift_vertex hp σ e he

@[simp]
theorem simplexEquiv_base (n : SimplexCategory) (τ : SingularSimplex E n) :
    (simplexEquiv hp n τ).1 = (projection hp).comp τ := rfl

@[simp]
theorem simplexEquiv_point (n : SimplexCategory) (τ : SingularSimplex E n) :
    (simplexEquiv hp n τ).2.1 = τ (stdSimplex.vertex 0) := rfl

/-- Covering transport inside a simplex uses its actual path class. -/
def simplexTransport {n : SimplexCategory} (σ : SingularSimplex B n)
    (x y : _root_.stdSimplex ℝ (Fin (n.len + 1))) :
    {e : E // p e = σ x} → {e : E // p e = σ y} :=
  hp.monodromy (.mk ((PathConnectedSpace.somePath x y).map σ.continuous))

/-- Transport along any path in the simplex agrees with simplex transport. -/
theorem simplexTransport_eq_path {n : SimplexCategory} (σ : SingularSimplex B n)
    {x y : _root_.stdSimplex ℝ (Fin (n.len + 1))} (q : Path x y) :
    simplexTransport hp σ x y = hp.monodromy (.mk (q.map σ.continuous)) := by
  unfold simplexTransport
  congr 1
  exact Path.Homotopic.Quotient.eq.mpr ((stdSimplex.paths_homotopic _ q).map σ)

/-- A lifted simplex transports its initial point to its value at the endpoint. -/
theorem simplexTransport_projection {n : SimplexCategory} (τ : SingularSimplex E n)
    (x y : _root_.stdSimplex ℝ (Fin (n.len + 1))) :
    simplexTransport hp ((projection hp).comp τ) x y ⟨τ x, rfl⟩ = ⟨τ y, rfl⟩ := by
  exact hp.monodromy_map (.mk ((PathConnectedSpace.somePath x y).map τ.continuous))

/-- The first vertex of a restricted lifted simplex is the monodromy-transported vertex. -/
theorem simplexTransport_lift {n : SimplexCategory} (σ : SingularSimplex B n)
    (e : E) (he : p e = σ (stdSimplex.vertex 0))
    (y : _root_.stdSimplex ℝ (Fin (n.len + 1))) :
    (simplexTransport hp σ (stdSimplex.vertex 0) y ⟨e, he⟩).1 = lift hp σ e he y := by
  have hσ := projection_lift hp σ e he
  have h₀ := lift_vertex hp σ e he
  generalize hτ : lift hp σ e he = τ at hσ h₀ ⊢
  subst σ
  subst e
  exact congrArg Subtype.val (simplexTransport_projection hp τ (stdSimplex.vertex 0) y)

/-- Simplicial restriction on base simplices and their lifted first vertices. -/
def restrict {m n : SimplexCategory} (s : BasedSimplex p n) (α : m ⟶ n) :
    BasedSimplex p m :=
  ⟨restrictSimplex s.1 α,
    simplexTransport hp s.1 (stdSimplex.vertex 0) (stdSimplex.map α (stdSimplex.vertex 0)) s.2⟩

/-- The simplex equivalence respects every actual simplicial operator. -/
theorem simplexEquiv_restrict {m n : SimplexCategory} (τ : SingularSimplex E n)
    (α : m ⟶ n) :
    simplexEquiv hp m (restrictSimplex τ α) = restrict hp (simplexEquiv hp n τ) α := by
  apply Sigma.ext (show (projection hp).comp (restrictSimplex τ α) =
    restrictSimplex ((projection hp).comp τ) α from rfl)
  exact heq_of_eq (simplexTransport_projection hp τ _ _).symm

/-- Restricting a lift changes its first vertex by the genuine covering transport. -/
theorem lift_restrict {m n : SimplexCategory} (s : BasedSimplex p n) (α : m ⟶ n) :
    (simplexEquiv hp m).symm (restrict hp s α) =
      restrictSimplex ((simplexEquiv hp n).symm s) α := by
  apply (simplexEquiv hp m).injective
  simp only [Equiv.apply_symm_apply, simplexEquiv_restrict]

/-- The restriction operation is unital. -/
@[simp]
theorem restrict_id {n : SimplexCategory} (s : BasedSimplex p n) :
    restrict hp s (𝟙 n) = s := by
  apply (simplexEquiv hp n).symm.injective
  simp only [lift_restrict, restrictSimplex_id]

/-- Restrictions compose with the actual simplicial operators. -/
theorem restrict_comp {l m n : SimplexCategory} (s : BasedSimplex p n)
    (α : l ⟶ m) (β : m ⟶ n) :
    restrict hp s (α ≫ β) = restrict hp (restrict hp s β) α := by
  apply (simplexEquiv hp l).symm.injective
  simp only [lift_restrict, restrictSimplex_comp]

/-- The zeroth face transports along the edge from vertex zero to vertex one. -/
theorem restrict_firstFace_point {n : ℕ} (s : BasedSimplex p ⦋n + 1⦌) :
    (restrict hp s (SimplexCategory.δ 0)).2.1 =
      (simplexTransport hp s.1 (stdSimplex.vertex 0) (stdSimplex.vertex 1) s.2).1 := by
  change (simplexTransport hp s.1 (stdSimplex.vertex 0)
    (stdSimplex.map (SimplexCategory.δ 0) (stdSimplex.vertex 0)) s.2).1 = _
  rw [simplexTransport_lift, simplexTransport_lift]
  simp [SimplexCategory.coe_δ]

/-- Every nonzero face retains the original point in the covering fiber. -/
theorem restrict_laterFace_point {n : ℕ} (s : BasedSimplex p ⦋n + 1⦌)
    (i : Fin (n + 1)) :
    (restrict hp s (SimplexCategory.δ i.succ)).2.1 = s.2.1 := by
  rw [show (restrict hp s (SimplexCategory.δ i.succ)).2.1 =
      lift hp s.1 s.2.1 s.2.2 (stdSimplex.map (SimplexCategory.δ i.succ) (stdSimplex.vertex 0)) from
    simplexTransport_lift hp _ _ _ _]
  simp [SimplexCategory.coe_δ]

/-- Every degeneracy retains the original point in the covering fiber. -/
theorem restrict_degeneracy_point {n : ℕ} (s : BasedSimplex p ⦋n⦌)
    (i : Fin (n + 1)) :
    (restrict hp s (SimplexCategory.σ i)).2.1 = s.2.1 := by
  rw [show (restrict hp s (SimplexCategory.σ i)).2.1 =
      lift hp s.1 s.2.1 s.2.2 (stdSimplex.map (SimplexCategory.σ i) (stdSimplex.vertex 0)) from
    simplexTransport_lift hp _ _ _ _]
  simp [SimplexCategory.coe_σ]

/-- The unique lift is natural under an actual commuting square of covering maps. -/
theorem map_lift {E' : Type u'} {B' : Type v'}
    [TopologicalSpace E'] [TopologicalSpace B'] {p' : E' → B'}
    (hp' : IsCoveringMap p') (k : C(E, E')) (f : C(B, B'))
    (h : ∀ e, p' (k e) = f (p e)) {n : SimplexCategory}
    (σ : SingularSimplex B n) (e : E) (he : p e = σ (stdSimplex.vertex 0)) :
    k.comp (lift hp σ e he) =
      lift hp' (f.comp σ) (k e) ((h e).trans (congrArg f he)) := by
  apply eq_lift hp'
  · ext x
    change p' (k (lift hp σ e he x)) = f (σ x)
    rw [h]
    exact congrArg f (ContinuousMap.congr_fun (projection_lift hp σ e he) x)
  · change k (lift hp σ e he (stdSimplex.vertex 0)) = k e
    rw [lift_vertex]

end IsCoveringMap
