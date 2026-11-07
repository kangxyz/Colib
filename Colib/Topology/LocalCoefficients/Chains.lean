/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.Basic
public import Colib.Topology.Realization.SimplexConnectivity
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.AlgebraicTopology.SingularHomology.Basic

/-!
Extracted from `Quillen/Topology/LocalCoefficients/Chains.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Definitions and proofs use the native
fundamental groupoid, simplicial modules, and Mathlib chain and homology functors.
Singular simplices use the pinned native `Convexity.StdSimplex` directly,
with their finitely supported weights, original vertices and maps.

# Singular chains with local coefficients

The module in degree `n` is the coproduct, over actual continuous singular
`n`-simplices, of the coefficient module at the first vertex. Coefficient
transport within a simplex is defined using genuine paths. Its coherence
follows from explicit endpoint-fixed homotopies in the standard simplex.
-/

@[expose] public section

open Convexity

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace FundamentalGroupoid.LocalCoefficients

variable {X : Type u} [TopologicalSpace X]

/-- Actual continuous singular simplices, without forgetting their parametrization. -/
abbrev SingularSimplex (X : Type u) [TopologicalSpace X] (n : SimplexCategory) :=
  C(StdSimplex ℝ (Fin (n.len + 1)), X)

/-- The coefficient module at the first vertex of a singular simplex. -/
abbrev simplexFiber (A : System.{u, u} X) {n : SimplexCategory}
    (σ : SingularSimplex X n) : ModuleCat.{u} ℤ :=
  fiber A (σ (StdSimplex.single 0))

/-- The actual direct sum of local coefficient modules in one singular degree. -/
def chainModule (A : System.{u, u} X) (n : SimplexCategory) : ModuleCat.{u} ℤ :=
  ∐ fun σ : SingularSimplex X n ↦ simplexFiber A σ

/-- Inclusion of a simplex with its coefficient at the first vertex. -/
def chainInclusion (A : System.{u, u} X) {n : SimplexCategory}
    (σ : SingularSimplex X n) : simplexFiber A σ ⟶ chainModule A n :=
  Sigma.ι (fun τ : SingularSimplex X n ↦ simplexFiber A τ) σ

/-- Transport between points of a singular simplex. Any path inside the
standard simplex gives the same answer, by endpoint-fixed homotopy. -/
def simplexTransport (A : System.{u, u} X) {n : SimplexCategory}
    (σ : SingularSimplex X n) (x y : StdSimplex ℝ (Fin (n.len + 1))) :
    fiber A (σ x) ⟶ fiber A (σ y) :=
  transport A ((PathConnectedSpace.somePath x y).map σ.continuous)

/-- The definition agrees with transport along every specified simplex path. -/
theorem simplexTransport_eq_path (A : System.{u, u} X) {n : SimplexCategory}
    (σ : SingularSimplex X n) {x y : StdSimplex ℝ (Fin (n.len + 1))}
    (p : Path x y) :
    simplexTransport A σ x y = transport A (p.map σ.continuous) :=
  transport_eq_of_homotopic A ((StdSimplex.paths_homotopic _ p).map σ)

@[simp]
theorem simplexTransport_self (A : System.{u, u} X) {n : SimplexCategory}
    (σ : SingularSimplex X n) (x : StdSimplex ℝ (Fin (n.len + 1))) :
    simplexTransport A σ x x = 𝟙 (fiber A (σ x)) := by
  rw [simplexTransport_eq_path A σ (Path.refl x)]
  exact transport_refl A (σ x)

/-- The first nontrivial coefficient identity: transport around two sides
of a singular triangle equals transport along the third side. -/
@[reassoc]
theorem simplexTransport_comp (A : System.{u, u} X) {n : SimplexCategory}
    (σ : SingularSimplex X n) (x y z : StdSimplex ℝ (Fin (n.len + 1))) :
    simplexTransport A σ x y ≫ simplexTransport A σ y z =
      simplexTransport A σ x z := by
  rw [simplexTransport_eq_path A σ
    ((PathConnectedSpace.somePath x y).trans (PathConnectedSpace.somePath y z))]
  rw [Path.map_trans, transport_trans]
  rfl

/-- Reparametrizing a singular simplex preserves its actual coefficient transport. -/
theorem simplexTransport_precomp (A : System.{u, u} X) {m n : SimplexCategory}
    (σ : SingularSimplex X n)
    (f : C(StdSimplex ℝ (Fin (m.len + 1)), StdSimplex ℝ (Fin (n.len + 1))))
    (x y : StdSimplex ℝ (Fin (m.len + 1))) :
    simplexTransport A (σ.comp f) x y = simplexTransport A σ (f x) (f y) := by
  rw [simplexTransport_eq_path A σ ((PathConnectedSpace.somePath x y).map f.continuous)]
  rfl

/-- Restriction along an arbitrary simplicial operator. -/
def restrictSimplex {m n : SimplexCategory} (σ : SingularSimplex X n) (α : m ⟶ n) :
    SingularSimplex X m :=
  σ.comp ⟨StdSimplex.map α, StdSimplex.continuous_map ℝ α⟩

/-- The coefficient of a restricted simplex is transported from the original
first vertex to the image of the new first vertex. -/
def restrictionTransport (A : System.{u, u} X) {m n : SimplexCategory}
    (σ : SingularSimplex X n) (α : m ⟶ n) :
    simplexFiber A σ ⟶ simplexFiber A (restrictSimplex σ α) :=
  simplexTransport A σ (StdSimplex.single 0) (StdSimplex.map α (StdSimplex.single 0))

/-- The linear map on actual direct sums induced by a simplicial operator. -/
def chainMap (A : System.{u, u} X) {m n : SimplexCategory} (α : m ⟶ n) :
    chainModule A n ⟶ chainModule A m :=
  Sigma.desc fun σ ↦ restrictionTransport A σ α ≫ chainInclusion A (restrictSimplex σ α)

@[reassoc (attr := simp)]
theorem chainInclusion_chainMap (A : System.{u, u} X) {m n : SimplexCategory}
    (α : m ⟶ n) (σ : SingularSimplex X n) :
    chainInclusion A σ ≫ chainMap A α =
      restrictionTransport A σ α ≫ chainInclusion A (restrictSimplex σ α) := by
  exact Sigma.ι_comp_desc _ _

@[simp]
theorem restrictSimplex_id {n : SimplexCategory} (σ : SingularSimplex X n) :
    restrictSimplex σ (𝟙 n) = σ := by
  ext x
  change σ (StdSimplex.map id x) = σ x
  rw [StdSimplex.map_id]

theorem restrictSimplex_comp {l m n : SimplexCategory} (σ : SingularSimplex X n)
    (α : l ⟶ m) (β : m ⟶ n) :
    restrictSimplex σ (α ≫ β) = restrictSimplex (restrictSimplex σ β) α := by
  ext x
  change σ (StdSimplex.map (β ∘ α) x) = σ (StdSimplex.map β (StdSimplex.map α x))
  rw [StdSimplex.map_comp]

/-- Changing a simplex index changes its summand by the canonical equality map. -/
theorem chainInclusion_congr (A : System.{u, u} X) {n : SimplexCategory}
    {σ τ : SingularSimplex X n} (h : σ = τ) :
    eqToHom (congrArg (simplexFiber A) h) ≫ chainInclusion A τ = chainInclusion A σ := by
  subst τ
  simp

/-- Transport to an equal endpoint is precisely the canonical equality map. -/
theorem simplexTransport_eqToHom (A : System.{u, u} X) {n : SimplexCategory}
    (σ : SingularSimplex X n) {x y : StdSimplex ℝ (Fin (n.len + 1))} (h : x = y) :
    simplexTransport A σ x y = eqToHom (congrArg (fun z ↦ fiber A (σ z)) h) := by
  subst y
  simp

/-- Endpoint equality is compatible with genuine simplex transport. -/
theorem simplexTransport_change_target (A : System.{u, u} X) {n : SimplexCategory}
    (σ : SingularSimplex X n) (x : StdSimplex ℝ (Fin (n.len + 1)))
    {y z : StdSimplex ℝ (Fin (n.len + 1))} (h : y = z) :
    simplexTransport A σ x y ≫ eqToHom (congrArg (fun t ↦ fiber A (σ t)) h) =
      simplexTransport A σ x z := by
  subst z
  simp

@[simp]
theorem chainMap_id (A : System.{u, u} X) (n : SimplexCategory) :
    chainMap A (𝟙 n) = 𝟙 (chainModule A n) := by
  apply Sigma.hom_ext
  intro σ
  change chainInclusion A σ ≫ chainMap A (𝟙 n) = chainInclusion A σ ≫ 𝟙 _
  rw [chainInclusion_chainMap, Category.comp_id]
  have h : restrictionTransport A σ (𝟙 n) =
      eqToHom (congrArg (simplexFiber A) (restrictSimplex_id σ).symm) :=
    simplexTransport_eqToHom A σ (StdSimplex.map_id _).symm
  rw [h]
  exact chainInclusion_congr A (restrictSimplex_id σ).symm

/-- The coefficient part of two successive restrictions is composition of
transport, with the explicit equality map between the two simplex indices. -/
theorem restrictionTransport_comp (A : System.{u, u} X) {l m n : SimplexCategory}
    (σ : SingularSimplex X n) (α : l ⟶ m) (β : m ⟶ n) :
    restrictionTransport A σ β ≫ restrictionTransport A (restrictSimplex σ β) α =
      restrictionTransport A σ (α ≫ β) ≫
        eqToHom (congrArg (simplexFiber A) (restrictSimplex_comp σ α β)) := by
  unfold restrictionTransport
  dsimp only [restrictSimplex]
  rw [simplexTransport_precomp]
  change simplexTransport A σ (StdSimplex.single 0) (StdSimplex.map β (StdSimplex.single 0)) ≫
    simplexTransport A σ (StdSimplex.map β (StdSimplex.single 0))
      (StdSimplex.map β (StdSimplex.map α (StdSimplex.single 0))) = _
  rw [simplexTransport_comp]
  exact (simplexTransport_change_target A σ (StdSimplex.single 0)
    (StdSimplex.map_comp (StdSimplex.single 0) α β)).symm

/-- Simplicial restriction of chains composes contravariantly. -/
@[reassoc]
theorem chainMap_comp (A : System.{u, u} X) {l m n : SimplexCategory}
    (α : l ⟶ m) (β : m ⟶ n) :
    chainMap A (α ≫ β) = chainMap A β ≫ chainMap A α := by
  apply Sigma.hom_ext
  intro σ
  change chainInclusion A σ ≫ chainMap A (α ≫ β) =
    chainInclusion A σ ≫ (chainMap A β ≫ chainMap A α)
  simp only [chainInclusion_chainMap, chainInclusion_chainMap_assoc]
  rw [← Category.assoc, restrictionTransport_comp, Category.assoc,
    chainInclusion_congr A (restrictSimplex_comp σ α β)]

/-- The first face starts at the second vertex of the original simplex. -/
@[simp]
theorem restrictSimplex_firstFace_vertex {n : ℕ} (σ : SingularSimplex X ⦋n + 1⦌) :
    restrictSimplex σ (SimplexCategory.δ 0) (StdSimplex.single 0) =
      σ (StdSimplex.single 1) := by
  simp [restrictSimplex, SimplexCategory.coe_δ]

/-- Every other face retains the original first vertex. -/
@[simp]
theorem restrictSimplex_laterFace_vertex {n : ℕ} (σ : SingularSimplex X ⦋n + 1⦌)
    (i : Fin (n + 1)) :
    restrictSimplex σ (SimplexCategory.δ i.succ) (StdSimplex.single 0) =
      σ (StdSimplex.single 0) := by
  simp [restrictSimplex, SimplexCategory.coe_δ]

/-- The zeroth face uses the actual edge transport from vertex zero to vertex one. -/
theorem restrictionTransport_firstFace (A : System.{u, u} X) {n : ℕ}
    (σ : SingularSimplex X ⦋n + 1⦌) :
    restrictionTransport A σ (SimplexCategory.δ 0) ≫
        eqToHom (congrArg (fiber A) (restrictSimplex_firstFace_vertex σ)) =
      simplexTransport A σ (StdSimplex.single 0) (StdSimplex.single 1) := by
  exact simplexTransport_change_target A σ (StdSimplex.single 0)
    (by simp [SimplexCategory.coe_δ])

/-- Nonzero faces use only the equality identification at the unchanged first vertex. -/
theorem restrictionTransport_laterFace (A : System.{u, u} X) {n : ℕ}
    (σ : SingularSimplex X ⦋n + 1⦌) (i : Fin (n + 1)) :
    restrictionTransport A σ (SimplexCategory.δ i.succ) =
      eqToHom (congrArg (fiber A) (restrictSimplex_laterFace_vertex σ i).symm) := by
  exact simplexTransport_eqToHom A σ
    (by simp [SimplexCategory.coe_δ])

/-- The simplicial module of singular chains with the actual local system.
Its simplicial identities are the preceding transport identities. -/
def simplicialModule (A : System.{u, u} X) : SimplicialObject (ModuleCat.{u} ℤ) where
  obj n := chainModule A n.unop
  map α := chainMap A α.unop
  map_id n := chainMap_id A n.unop
  map_comp α β := chainMap_comp A β.unop α.unop

/-- Singular chains with arbitrary integral local coefficients. The
alternating-face construction proves the differential squares to zero. -/
def singularChainComplex (A : System.{u, u} X) : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj (simplicialModule A)

/-- The boundary on each actual simplex, including transport on its first face. -/
@[reassoc]
theorem chainInclusion_d (A : System.{u, u} X) {n : ℕ}
    (σ : SingularSimplex X ⦋n + 1⦌) :
    chainInclusion A σ ≫ (singularChainComplex A).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        (restrictionTransport A σ (SimplexCategory.δ i) ≫
          chainInclusion A (restrictSimplex σ (SimplexCategory.δ i))) := by
  simp [singularChainComplex, AlgebraicTopology.AlternatingFaceMapComplex.objD,
    simplicialModule, SimplicialObject.δ, Preadditive.comp_sum]

/-- The actual local-coefficient differential squares to zero in every degree. -/
@[reassoc]
theorem singularChainComplex_d_squared (A : System.{u, u} X) (n : ℕ) :
    (singularChainComplex A).d (n + 2) (n + 1) ≫
      (singularChainComplex A).d (n + 1) n = 0 :=
  (singularChainComplex A).d_comp_d _ _ _

/-- In constant coefficients, the degreewise comparison merely reindexes
actual continuous simplices by mathlib's equivalent singular-simplex type. -/
def constantModuleIso (V : ModuleCat.{u} ℤ) (n : SimplexCategoryᵒᵖ) :
    chainModule (constant X V) n.unop ≅
      ((TopCat.toSSet.obj (TopCat.of X)) ⋙ sigmaConst.obj V).obj n where
  hom := Sigma.desc fun σ ↦ Sigma.ι (fun _ ↦ V)
    (((TopCat.of X).toSSetObjEquiv n).symm σ)
  inv := Sigma.desc fun σ ↦ chainInclusion (constant X V)
    (((TopCat.of X).toSSetObjEquiv n) σ)
  hom_inv_id := by
    apply Sigma.hom_ext
    intro σ
    simp [chainInclusion, constant, chainModule]
  inv_hom_id := by
    apply Sigma.hom_ext
    intro σ
    simp [chainInclusion, constant, chainModule]

/-- The constant local system recovers the ordinary simplicial singular module. -/
def constantSimplicialIso (V : ModuleCat.{u} ℤ) :
    simplicialModule (constant X V) ≅
      (TopCat.toSSet.obj (TopCat.of X)) ⋙ sigmaConst.obj V :=
  NatIso.ofComponents (constantModuleIso V) (by
    intro n m α
    apply Sigma.hom_ext
    intro σ
    simp [simplicialModule, chainMap, restrictionTransport, simplexTransport,
      transport, constant, chainInclusion, constantModuleIso, sigmaConst, Sigma.map']
    rfl)

/-- Constant local coefficients agree with mathlib's genuine singular chain complex. -/
def constantChainComplexIso (V : ModuleCat.{u} ℤ) :
    singularChainComplex (constant X V) ≅
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj V).obj
        (TopCat.of X) :=
  (AlgebraicTopology.alternatingFaceMapComplex _).mapIso (constantSimplicialIso V)

end FundamentalGroupoid.LocalCoefficients
