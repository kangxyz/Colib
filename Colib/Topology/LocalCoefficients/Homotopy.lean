/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.Prism
/-!
Adapted from `Quillen/Topology/LocalCoefficients/Homotopy.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using the pinned native singular
simplices, module coproducts, and chain/homology functors.

# Homotopy invariance of actual local-coefficient chains

A continuous homotopy induces a chain homotopy after converting the source
coefficient system by transport along its point tracks. The construction uses
actual singular prism simplices and the first-edge transport proved in
`Prism`. All face and degeneracy identities are proved for the transported
coproduct maps before applying mathlib's alternating-face chain-homotopy functor.
-/

@[expose] public section

open CategoryTheory Limits Opposite
open scoped Simplicial
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
namespace FundamentalGroupoid.LocalCoefficients
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  {f g : C(X, Y)}
/-- A simplex summand with its first-vertex coefficient identified with a specified point. -/
def anchoredInclusion (A : System.{u, u} Y) {n : SimplexCategory}
    (σ : SingularSimplex Y n) (y : Y) (h : y = σ (stdSimplex.vertex 0)) :
    fiber A y ⟶ chainModule A n :=
  eqToHom (congrArg (fiber A) h) ≫ chainInclusion A σ

theorem anchoredInclusion_congr (A : System.{u, u} Y) {n : SimplexCategory}
    {σ τ : SingularSimplex Y n} (h : σ = τ) (y : Y)
    (hσ : y = σ (stdSimplex.vertex 0)) (hτ : y = τ (stdSimplex.vertex 0)) :
    anchoredInclusion A σ y hσ = anchoredInclusion A τ y hτ := by
  subst τ
  rfl

theorem restrictSimplex_vertex_of_zero {m n : SimplexCategory}
    (σ : SingularSimplex Y n) (α : m ⟶ n) (hα : α 0 = 0) :
    restrictSimplex σ α (stdSimplex.vertex 0) = σ (stdSimplex.vertex 0) := by
  simp [restrictSimplex, hα]

theorem anchoredInclusion_chainMap (A : System.{u, u} Y) {m n : SimplexCategory}
    (σ : SingularSimplex Y n) (y : Y) (hσ : y = σ (stdSimplex.vertex 0))
    (α : m ⟶ n) (hα : α 0 = 0) :
    anchoredInclusion A σ y hσ ≫ chainMap A α =
      anchoredInclusion A (restrictSimplex σ α) y
        (hσ.trans (restrictSimplex_vertex_of_zero σ α hα).symm) := by
  have ht : restrictionTransport A σ α =
      eqToHom (congrArg (fiber A) (restrictSimplex_vertex_of_zero σ α hα).symm) :=
    simplexTransport_eqToHom A σ (by simp [hα])
  simp only [anchoredInclusion, Category.assoc, chainInclusion_chainMap, ht,
    eqToHom_trans_assoc]

/-- The transported inclusion of one actual prism simplex. -/
def prismInclusion (H : f.Homotopy g) (A : System.{u, u} Y) {n : ℕ}
    (i : Fin (n + 1)) (σ : SingularSimplex X ⦋n⦌) :
    simplexFiber (pullback f A) σ ⟶ chainModule A ⦋n + 1⦌ :=
  anchoredInclusion A (prismSimplex H i σ) (f (σ (stdSimplex.vertex 0)))
    (prismSimplex_first_vertex H i σ).symm

/-- The prism operator on the actual direct sums of local coefficient modules. -/
def prismModuleMap (H : f.Homotopy g) (A : System.{u, u} Y) {n : ℕ}
    (i : Fin (n + 1)) : chainModule (pullback f A) ⦋n⦌ ⟶ chainModule A ⦋n + 1⦌ :=
  Sigma.desc fun σ ↦ prismInclusion H A i σ

@[reassoc (attr := simp)]
theorem chainInclusion_prismModuleMap (H : f.Homotopy g) (A : System.{u, u} Y) {n : ℕ}
    (i : Fin (n + 1)) (σ : SingularSimplex X ⦋n⦌) :
    chainInclusion (pullback f A) σ ≫ prismModuleMap H A i = prismInclusion H A i σ :=
  Sigma.ι_desc _ _

theorem prismModuleMap_last_face (H : f.Homotopy g) (A : System.{u, u} Y) (n : ℕ) :
    prismModuleMap H A (Fin.last n) ≫ chainMap A (SimplexCategory.δ (Fin.last (n + 1))) =
      pushforwardModuleMap f A ⦋n⦌ := by
  apply Sigma.hom_ext
  intro σ
  change chainInclusion (pullback f A) σ ≫ (_ ≫ _) = chainInclusion (pullback f A) σ ≫ _
  rw [chainInclusion_prismModuleMap_assoc, chainInclusion_pushforwardModuleMap]
  unfold prismInclusion
  rw [anchoredInclusion_chainMap A _ _ _ _ (by simp [SimplexCategory.coe_δ])]
  exact anchoredInclusion_congr A (prismSimplex_face_last H σ) _ _ rfl
end FundamentalGroupoid.LocalCoefficients
namespace FundamentalGroupoid.LocalCoefficients
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {f g : C(X, Y)}
theorem eqToHom_anchoredInclusion (A : System.{u, u} Y) {n : SimplexCategory}
    (σ : SingularSimplex Y n) {y y' : Y} (h : y = y')
    (hσ : y' = σ (stdSimplex.vertex 0)) :
    eqToHom (congrArg (fiber A) h) ≫ anchoredInclusion A σ y' hσ =
      anchoredInclusion A σ y (h.trans hσ) := by
  simp only [anchoredInclusion, eqToHom_trans_assoc]

theorem prismInclusion_restrict_of_zero (H : f.Homotopy g) (A : System.{u, u} Y)
    {m n : ℕ} (i : Fin (n + 1)) (j : Fin (m + 1))
    (σ : SingularSimplex X ⦋n⦌)
    (α : ⦋m + 1⦌ ⟶ ⦋n + 1⦌) (β : ⦋m⦌ ⟶ ⦋n⦌)
    (hα : α 0 = 0) (hβ : β 0 = 0)
    (h : restrictSimplex (prismSimplex H i σ) α = prismSimplex H j (restrictSimplex σ β)) :
    prismInclusion H A i σ ≫ chainMap A α =
      restrictionTransport (pullback f A) σ β ≫
        prismInclusion H A j (restrictSimplex σ β) := by
  have ht : restrictionTransport (pullback f A) σ β =
      eqToHom (congrArg (fiber (pullback f A))
        (restrictSimplex_vertex_of_zero σ β hβ).symm) :=
    simplexTransport_eqToHom (pullback f A) σ (by simp [hβ])
  rw [ht]
  unfold prismInclusion
  rw [anchoredInclusion_chainMap A _ _ _ α hα]
  change anchoredInclusion A _ _ _ =
    eqToHom (congrArg (fiber A) (congrArg f
      (restrictSimplex_vertex_of_zero σ β hβ).symm)) ≫ _
  rw [eqToHom_anchoredInclusion A _
    (congrArg f (restrictSimplex_vertex_of_zero σ β hβ).symm)]
  exact anchoredInclusion_congr A h _ _ _

theorem prismModuleMap_middle_face (H : f.Homotopy g) (A : System.{u, u} Y)
    {n : ℕ} (j : Fin (n + 1)) :
    prismModuleMap H A j.succ ≫ chainMap A (SimplexCategory.δ j.castSucc.succ) =
      prismModuleMap H A j.castSucc ≫ chainMap A (SimplexCategory.δ j.castSucc.succ) := by
  apply Sigma.hom_ext
  intro σ
  change chainInclusion (pullback f A) σ ≫ (_ ≫ _) =
    chainInclusion (pullback f A) σ ≫ (_ ≫ _)
  rw [chainInclusion_prismModuleMap_assoc, chainInclusion_prismModuleMap_assoc]
  unfold prismInclusion
  rw [anchoredInclusion_chainMap A _ _ _ _ (by simp [SimplexCategory.coe_δ]),
    anchoredInclusion_chainMap A _ _ _ _ (by simp [SimplexCategory.coe_δ])]
  exact anchoredInclusion_congr A (prismSimplex_middle_face H j σ) _ _ _

theorem prismModuleMap_degeneracy_of_le (H : f.Homotopy g) (A : System.{u, u} Y)
    {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    prismModuleMap H A j ≫ chainMap A (SimplexCategory.σ i.castSucc) =
      chainMap (pullback f A) (SimplexCategory.σ i) ≫ prismModuleMap H A j.succ := by
  apply Sigma.hom_ext
  intro σ
  change chainInclusion (pullback f A) σ ≫ (_ ≫ _) =
    chainInclusion (pullback f A) σ ≫ (_ ≫ _)
  rw [chainInclusion_prismModuleMap_assoc, chainInclusion_chainMap_assoc,
    chainInclusion_prismModuleMap]
  exact prismInclusion_restrict_of_zero H A j j.succ σ _ _
    (by simp [SimplexCategory.coe_σ]) (by simp [SimplexCategory.coe_σ])
    (prismSimplex_degeneracy_of_le H i j hij σ)

theorem prismModuleMap_degeneracy_of_ge (H : f.Homotopy g) (A : System.{u, u} Y)
    {n : ℕ} (i j : Fin (n + 1)) (hji : j ≤ i) :
    prismModuleMap H A j ≫ chainMap A (SimplexCategory.σ i.succ) =
      chainMap (pullback f A) (SimplexCategory.σ i) ≫ prismModuleMap H A j.castSucc := by
  apply Sigma.hom_ext
  intro σ
  change chainInclusion (pullback f A) σ ≫ (_ ≫ _) =
    chainInclusion (pullback f A) σ ≫ (_ ≫ _)
  rw [chainInclusion_prismModuleMap_assoc, chainInclusion_chainMap_assoc,
    chainInclusion_prismModuleMap]
  exact prismInclusion_restrict_of_zero H A j j.castSucc σ _ _
    (by simp [SimplexCategory.coe_σ]) (by simp [SimplexCategory.coe_σ])
    (prismSimplex_degeneracy_of_ge H i j hji σ)
end FundamentalGroupoid.LocalCoefficients
namespace FundamentalGroupoid.LocalCoefficients
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {f g : C(X, Y)}
theorem anchoredInclusion_first_face (A : System.{u, u} Y) {n : ℕ}
    (σ : SingularSimplex Y ⦋n + 1⦌) (τ : SingularSimplex Y ⦋n⦌) (x y : Y)
    (hx : x = σ (stdSimplex.vertex 0)) (hy : y = σ (stdSimplex.vertex 1))
    (hτ : y = τ (stdSimplex.vertex 0))
    (h : restrictSimplex σ (SimplexCategory.δ 0) = τ) :
    anchoredInclusion A σ x hx ≫ chainMap A (SimplexCategory.δ 0) =
      (eqToHom (congrArg (fiber A) hx) ≫
        simplexTransport A σ (stdSimplex.vertex 0) (stdSimplex.vertex 1) ≫
          eqToHom (congrArg (fiber A) hy.symm)) ≫ anchoredInclusion A τ y hτ := by
  rw [← restrictionTransport_firstFace A σ]
  simp only [anchoredInclusion, Category.assoc, chainInclusion_chainMap,
    eqToHom_trans_assoc]
  rw [← chainInclusion_congr A h]

theorem prismModuleMap_first_face (H : f.Homotopy g) (A : System.{u, u} Y) (n : ℕ) :
    prismModuleMap H A (0 : Fin (n + 1)) ≫ chainMap A (SimplexCategory.δ 0) =
      coefficientModuleMap (homotopyPullbackIso H A).hom ⦋n⦌ ≫
        pushforwardModuleMap g A ⦋n⦌ := by
  apply Sigma.hom_ext
  intro σ
  change chainInclusion (pullback f A) σ ≫ (_ ≫ _) =
    chainInclusion (pullback f A) σ ≫ (_ ≫ _)
  rw [chainInclusion_prismModuleMap_assoc, chainInclusion_coefficientModuleMap_assoc,
    chainInclusion_pushforwardModuleMap, homotopyPullbackIso_hom_app]
  unfold prismInclusion
  rw [anchoredInclusion_first_face A _ (g.comp σ) _ (g (σ (stdSimplex.vertex 0))) _
    (prismSimplex_zero_second_vertex H σ).symm rfl (prismSimplex_face_zero H σ),
    prismSimplex_zero_edge_transport]
  simp [anchoredInclusion]

theorem prismInclusion_first_face_succ (H : f.Homotopy g) (A : System.{u, u} Y)
    {n : ℕ} (j : Fin (n + 1)) (σ : SingularSimplex X ⦋n + 1⦌) :
    prismInclusion H A j.succ σ ≫ chainMap A (SimplexCategory.δ 0) =
      restrictionTransport (pullback f A) σ (SimplexCategory.δ 0) ≫
        prismInclusion H A j (restrictSimplex σ (SimplexCategory.δ 0)) := by
  unfold prismInclusion
  rw [anchoredInclusion_first_face A _
    (prismSimplex H j (restrictSimplex σ (SimplexCategory.δ 0))) _
    (f (σ (stdSimplex.vertex 1))) _ (prismSimplex_succ_second_vertex H j σ).symm
    (by rw [prismSimplex_first_vertex, restrictSimplex_firstFace_vertex])
    (prismSimplex_face_of_le H 0 j (by simp) σ)]
  rw [prismSimplex_succ_edge_transport, ← restrictionTransport_firstFace (pullback f A) σ]
  simp only [Category.assoc, anchoredInclusion, eqToHom_trans_assoc]
end FundamentalGroupoid.LocalCoefficients
namespace FundamentalGroupoid.LocalCoefficients
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {f g : C(X, Y)}
theorem prismModuleMap_face_of_le (H : f.Homotopy g) (A : System.{u, u} Y)
    {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc) :
    prismModuleMap H A j.succ ≫ chainMap A (SimplexCategory.δ i.castSucc) =
      chainMap (pullback f A) (SimplexCategory.δ i) ≫ prismModuleMap H A j := by
  apply Sigma.hom_ext
  intro σ
  change chainInclusion (pullback f A) σ ≫ (_ ≫ _) =
    chainInclusion (pullback f A) σ ≫ (_ ≫ _)
  rw [chainInclusion_prismModuleMap_assoc, chainInclusion_chainMap_assoc,
    chainInclusion_prismModuleMap]
  by_cases hi : i = 0
  · subst i
    exact prismInclusion_first_face_succ H A j σ
  · exact prismInclusion_restrict_of_zero H A j.succ j σ _ _
      (by simpa only [SimplexCategory.coe_δ] using
        Fin.succAbove_ne_zero_zero (by simpa using hi : i.castSucc ≠ 0))
      (by simpa only [SimplexCategory.coe_δ] using Fin.succAbove_ne_zero_zero hi)
      (prismSimplex_face_of_le H i j hij σ)

theorem prismModuleMap_face_of_lt (H : f.Homotopy g) (A : System.{u, u} Y)
    {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i) :
    prismModuleMap H A j.castSucc ≫ chainMap A (SimplexCategory.δ i.succ) =
      chainMap (pullback f A) (SimplexCategory.δ i) ≫ prismModuleMap H A j := by
  apply Sigma.hom_ext
  intro σ
  change chainInclusion (pullback f A) σ ≫ (_ ≫ _) =
    chainInclusion (pullback f A) σ ≫ (_ ≫ _)
  rw [chainInclusion_prismModuleMap_assoc, chainInclusion_chainMap_assoc,
    chainInclusion_prismModuleMap]
  have hi : i ≠ 0 := by intro hi; simp [hi] at hji
  exact prismInclusion_restrict_of_zero H A j.castSucc j σ _ _
    (by simp [SimplexCategory.coe_δ])
    (by simpa only [SimplexCategory.coe_δ] using Fin.succAbove_ne_zero_zero hi)
    (prismSimplex_face_of_lt H i j hji σ)

/-- The genuine simplicial homotopy, with the endpoint coefficient conversion explicit. -/
def pushforwardSimplicialHomotopy (H : f.Homotopy g) (A : System.{u, u} Y) :
    SimplicialObject.Homotopy (pushforwardSimplicialMap f A)
      (coefficientSimplicialMap (homotopyPullbackIso H A).hom ≫
        pushforwardSimplicialMap g A) where
  h i := prismModuleMap H A i
  h_zero_comp_δ_zero n := prismModuleMap_first_face H A n
  h_last_comp_δ_last n := prismModuleMap_last_face H A n
  h_succ_comp_δ_castSucc_of_lt i j hij := prismModuleMap_face_of_le H A i j hij
  h_succ_comp_δ_castSucc_succ j := prismModuleMap_middle_face H A j
  h_castSucc_comp_δ_succ_of_lt i j hji := prismModuleMap_face_of_lt H A i j hji
  h_comp_σ_castSucc_of_le i j hij := prismModuleMap_degeneracy_of_le H A i j hij
  h_comp_σ_succ_of_lt i j hji := prismModuleMap_degeneracy_of_ge H A i j hji

/-- Homotopic spatial maps induce chain-homotopic maps after transport of
coefficients along the specified homotopy. No homology equivalence is assumed. -/
def pushforwardChainHomotopy (H : f.Homotopy g) (A : System.{u, u} Y) :
    _root_.Homotopy (pushforwardChainMap f A)
      ((homotopyPullbackChainIso H A).hom ≫ pushforwardChainMap g A) :=
  (pushforwardSimplicialHomotopy H A).toChainHomotopy
end FundamentalGroupoid.LocalCoefficients
