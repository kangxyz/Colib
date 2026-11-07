/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.Chains
public import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
Adapted from `Quillen/Topology/LocalCoefficients/SmallChains.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps and signs.

# Cover-small singular chains with local coefficients

A simplex is small for a family of subsets if its entire image lies in one
member. The coproduct of the original coefficient fibers over these actual
small simplices is a simplicial module. Its alternating-face complex embeds
in the original twisted singular chain complex by the original summand maps.

No openness or covering hypothesis is needed for boundary closure. In
particular, this construction applies to open covers, but it does not assert
the small-chain quasi-isomorphism or excision. The degreewise projection used
to prove injectivity is not asserted to be a chain map.
-/

@[expose] public section

open Convexity

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u v

namespace FundamentalGroupoid.LocalCoefficients

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- The whole image of a simplex lies in a single member of the given family. -/
def IsCoverSmall (U : ι → Set X) {n : SimplexCategory} (σ : SingularSimplex X n) : Prop :=
  ∃ i, Set.range σ ⊆ U i

/-- Arbitrary continuous reparametrization preserves cover-smallness. -/
theorem IsCoverSmall.precomp {U : ι → Set X} {m n : SimplexCategory}
    {σ : SingularSimplex X n} (hσ : IsCoverSmall U σ)
    (f : C(StdSimplex ℝ (Fin (m.len + 1)), StdSimplex ℝ (Fin (n.len + 1)))) :
    IsCoverSmall U (σ.comp f) := by
  obtain ⟨i, hi⟩ := hσ
  exact ⟨i, fun _ ⟨x, hx⟩ ↦ hi ⟨f x, hx⟩⟩

/-- In particular, every face and degeneracy of a small simplex is small. -/
theorem IsCoverSmall.restrict {U : ι → Set X} {m n : SimplexCategory}
    {σ : SingularSimplex X n} (hσ : IsCoverSmall U σ) (α : m ⟶ n) :
    IsCoverSmall U (restrictSimplex σ α) :=
  hσ.precomp ⟨StdSimplex.map α, StdSimplex.continuous_map ℝ α⟩

/-- Actual small simplices, retaining their original continuous maps. -/
abbrev CoverSmallSimplex (U : ι → Set X) (n : SimplexCategory) :=
  {σ : SingularSimplex X n // IsCoverSmall U σ}

/-- Restriction of actual small simplices. -/
def restrictSmallSimplex (U : ι → Set X) {m n : SimplexCategory}
    (σ : CoverSmallSimplex U n) (α : m ⟶ n) : CoverSmallSimplex U m :=
  ⟨restrictSimplex σ.val α, σ.property.restrict α⟩

/-- The small-chain module is the actual direct sum of the original fibers. -/
def smallChainModule (U : ι → Set X) (A : System.{u, u} X)
    (n : SimplexCategory) : ModuleCat.{u} ℤ :=
  ∐ fun σ : CoverSmallSimplex U n ↦ simplexFiber A σ.val

/-- The summand map of a small simplex with its original coefficient fiber. -/
def smallChainInclusion (U : ι → Set X) (A : System.{u, u} X)
    {n : SimplexCategory} (σ : CoverSmallSimplex U n) :
    simplexFiber A σ.val ⟶ smallChainModule U A n :=
  Sigma.ι (fun τ : CoverSmallSimplex U n ↦ simplexFiber A τ.val) σ

/-- The original inclusion into all singular chains, without altering coefficients. -/
def smallModuleInclusion (U : ι → Set X) (A : System.{u, u} X)
    (n : SimplexCategory) : smallChainModule U A n ⟶ chainModule A n :=
  Sigma.desc fun σ ↦ chainInclusion A σ.val

@[reassoc (attr := simp)]
theorem smallChainInclusion_smallModuleInclusion (U : ι → Set X)
    (A : System.{u, u} X) {n : SimplexCategory} (σ : CoverSmallSimplex U n) :
    smallChainInclusion U A σ ≫ smallModuleInclusion U A n = chainInclusion A σ.val :=
  Sigma.ι_comp_desc _ _

/-- Projection onto small summands. This is only a degreewise map, not a chain map. -/
def smallModuleProjection (U : ι → Set X) (A : System.{u, u} X)
    (n : SimplexCategory) : chainModule A n ⟶ smallChainModule U A n := by
  classical
  exact Sigma.desc fun σ ↦ if hσ : IsCoverSmall U σ then
    smallChainInclusion U A ⟨σ, hσ⟩ else 0

/-- Small chains embed as a direct summand in each individual chain module. -/
@[reassoc (attr := simp)]
theorem smallModuleInclusion_projection (U : ι → Set X) (A : System.{u, u} X)
    (n : SimplexCategory) :
    smallModuleInclusion U A n ≫ smallModuleProjection U A n = 𝟙 _ := by
  classical
  apply Sigma.hom_ext
  intro σ
  change smallChainInclusion U A σ ≫ _ = smallChainInclusion U A σ ≫ _
  simp [smallModuleProjection, chainInclusion, σ.property]

/-- The original small-chain inclusion is genuinely monic in every degree. -/
instance smallModuleInclusion_mono (U : ι → Set X) (A : System.{u, u} X)
    (n : SimplexCategory) : Mono (smallModuleInclusion U A n) :=
  mono_of_mono_fac (smallModuleInclusion_projection U A n)

/-- Equivalently, the underlying map of modules is injective. -/
theorem smallModuleInclusion_injective (U : ι → Set X) (A : System.{u, u} X)
    (n : SimplexCategory) : Function.Injective (smallModuleInclusion U A n) :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

/-- Simplicial restriction on small chains uses the original transport. -/
def smallChainMap (U : ι → Set X) (A : System.{u, u} X)
    {m n : SimplexCategory} (α : m ⟶ n) :
    smallChainModule U A n ⟶ smallChainModule U A m :=
  Sigma.desc fun σ ↦ restrictionTransport A σ.val α ≫
    smallChainInclusion U A (restrictSmallSimplex U σ α)

@[reassoc (attr := simp)]
theorem smallChainInclusion_smallChainMap (U : ι → Set X) (A : System.{u, u} X)
    {m n : SimplexCategory} (α : m ⟶ n) (σ : CoverSmallSimplex U n) :
    smallChainInclusion U A σ ≫ smallChainMap U A α =
      restrictionTransport A σ.val α ≫
        smallChainInclusion U A (restrictSmallSimplex U σ α) :=
  Sigma.ι_comp_desc _ _

/-- Small restrictions are precisely the restrictions of the original chains. -/
@[reassoc (attr := simp)]
theorem smallChainMap_inclusion (U : ι → Set X) (A : System.{u, u} X)
    {m n : SimplexCategory} (α : m ⟶ n) :
    smallChainMap U A α ≫ smallModuleInclusion U A m =
      smallModuleInclusion U A n ≫ chainMap A α := by
  apply Sigma.hom_ext
  intro σ
  change smallChainInclusion U A σ ≫ _ = smallChainInclusion U A σ ≫ _
  simp
  rfl

@[simp]
theorem smallChainMap_id (U : ι → Set X) (A : System.{u, u} X) (n : SimplexCategory) :
    smallChainMap U A (𝟙 n) = 𝟙 _ := by
  apply (cancel_mono (smallModuleInclusion U A n)).mp
  simp

@[reassoc]
theorem smallChainMap_comp (U : ι → Set X) (A : System.{u, u} X)
    {l m n : SimplexCategory} (α : l ⟶ m) (β : m ⟶ n) :
    smallChainMap U A (α ≫ β) = smallChainMap U A β ≫ smallChainMap U A α := by
  apply (cancel_mono (smallModuleInclusion U A l)).mp
  simp [chainMap_comp, Category.assoc]

/-- A genuine simplicial submodule, constructed from actual small simplices. -/
def smallSimplicialModule (U : ι → Set X) (A : System.{u, u} X) :
    SimplicialObject (ModuleCat.{u} ℤ) where
  obj n := smallChainModule U A n.unop
  map α := smallChainMap U A α.unop
  map_id n := smallChainMap_id U A n.unop
  map_comp α β := smallChainMap_comp U A β.unop α.unop

/-- The natural inclusion of small simplicial chains into all simplicial chains. -/
def smallSimplicialInclusion (U : ι → Set X) (A : System.{u, u} X) :
    smallSimplicialModule U A ⟶ simplicialModule A where
  app n := smallModuleInclusion U A n.unop
  naturality _n _m α := smallChainMap_inclusion U A α.unop

/-- The actual twisted small-chain complex. Its differential is constructed,
not given as closure data or a homological hypothesis. -/
def smallChainComplex (U : ι → Set X) (A : System.{u, u} X) :
    ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj (smallSimplicialModule U A)

/-- The original inclusion of the twisted small-chain subcomplex. -/
def smallChainComplexInclusion (U : ι → Set X) (A : System.{u, u} X) :
    smallChainComplex U A ⟶ singularChainComplex A :=
  (AlgebraicTopology.alternatingFaceMapComplex _).map (smallSimplicialInclusion U A)

@[simp]
theorem smallChainComplexInclusion_f (U : ι → Set X) (A : System.{u, u} X) (n : ℕ) :
    (smallChainComplexInclusion U A).f n = smallModuleInclusion U A ⦋n⦌ := rfl

instance smallChainComplexInclusion_f_mono (U : ι → Set X)
    (A : System.{u, u} X) (n : ℕ) : Mono ((smallChainComplexInclusion U A).f n) :=
  smallModuleInclusion_mono U A ⦋n⦌

/-- The inclusion is also monic as a morphism of chain complexes. -/
instance smallChainComplexInclusion_mono (U : ι → Set X) (A : System.{u, u} X) :
    Mono (smallChainComplexInclusion U A) where
  right_cancellation f g h := by
    ext n : 1
    exact (cancel_mono ((smallChainComplexInclusion U A).f n)).mp
      (congrArg (fun k ↦ k.f n) h)

/-- The explicit twisted boundary closes on small chains, including its zeroth
face transport. Every target in this sum is an actual small-simplex summand. -/
@[reassoc]
theorem smallChainInclusion_d (U : ι → Set X) (A : System.{u, u} X) {n : ℕ}
    (σ : CoverSmallSimplex U ⦋n + 1⦌) :
    smallChainInclusion U A σ ≫ (smallChainComplex U A).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        (restrictionTransport A σ.val (SimplexCategory.δ i) ≫
          smallChainInclusion U A (restrictSmallSimplex U σ (SimplexCategory.δ i))) := by
  simp [smallChainComplex, AlgebraicTopology.AlternatingFaceMapComplex.objD,
    smallSimplicialModule, SimplicialObject.δ, Preadditive.comp_sum]

/-- The genuine restricted differential squares to zero. -/
@[reassoc]
theorem smallChainComplex_d_squared (U : ι → Set X) (A : System.{u, u} X) (n : ℕ) :
    (smallChainComplex U A).d (n + 2) (n + 1) ≫
      (smallChainComplex U A).d (n + 1) n = 0 :=
  (smallChainComplex U A).d_comp_d _ _ _

/-- The concrete small-chain submodule of the original chain module. -/
def smallChainSubmodule (U : ι → Set X) (A : System.{u, u} X) (n : ℕ) :
    Submodule ℤ ((singularChainComplex A).X n) :=
  LinearMap.range (smallModuleInclusion U A ⦋n⦌).hom

/-- The original twisted differential preserves the concrete small submodules. -/
theorem smallChainSubmodule_d_mem (U : ι → Set X) (A : System.{u, u} X)
    (i j : ℕ) {x : (singularChainComplex A).X i} (hx : x ∈ smallChainSubmodule U A i) :
    (singularChainComplex A).d i j x ∈ smallChainSubmodule U A j := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨(smallChainComplex U A).d i j y, ?_⟩
  exact congrArg (fun f ↦ f y) ((smallChainComplexInclusion U A).comm i j).symm

/-- If a family contains the whole space, every actual simplex is small. -/
theorem isCoverSmall_of_univ {U : ι → Set X} (hU : ∃ i, U i = Set.univ)
    {n : SimplexCategory} (σ : SingularSimplex X n) : IsCoverSmall U σ := by
  obtain ⟨i, hi⟩ := hU
  exact ⟨i, by rw [hi]; exact Set.subset_univ _⟩

/-- For the full cover, projection followed by inclusion is the identity too. -/
@[reassoc]
theorem smallModuleProjection_inclusion (U : ι → Set X) (A : System.{u, u} X)
    (n : SimplexCategory) (hU : ∀ σ : SingularSimplex X n, IsCoverSmall U σ) :
    smallModuleProjection U A n ≫ smallModuleInclusion U A n = 𝟙 _ := by
  classical
  apply Sigma.hom_ext
  intro σ
  simp [smallModuleProjection, hU σ, chainInclusion, chainModule]

/-- When every simplex is small, the original degreewise inclusion is an iso. -/
def smallModuleIso (U : ι → Set X) (A : System.{u, u} X) (n : SimplexCategory)
    (hU : ∀ σ : SingularSimplex X n, IsCoverSmall U σ) :
    smallChainModule U A n ≅ chainModule A n where
  hom := smallModuleInclusion U A n
  inv := smallModuleProjection U A n
  hom_inv_id := smallModuleInclusion_projection U A n
  inv_hom_id := smallModuleProjection_inclusion U A n hU

/-- The full-cover comparison is a genuine simplicial isomorphism. -/
def fullCoverSimplicialIso (U : ι → Set X) (A : System.{u, u} X)
    (hU : ∃ i, U i = Set.univ) : smallSimplicialModule U A ≅ simplicialModule A :=
  NatIso.ofComponents
    (fun n ↦ smallModuleIso U A n.unop (isCoverSmall_of_univ hU))
    (fun α ↦ smallChainMap_inclusion U A α.unop)

/-- A cover containing the whole space recovers the original twisted chains. -/
def fullCoverChainIso (U : ι → Set X) (A : System.{u, u} X)
    (hU : ∃ i, U i = Set.univ) : smallChainComplex U A ≅ singularChainComplex A :=
  (AlgebraicTopology.alternatingFaceMapComplex _).mapIso (fullCoverSimplicialIso U A hU)

/-- The full-cover comparison uses precisely the original inclusion. -/
@[simp]
theorem fullCoverChainIso_hom (U : ι → Set X) (A : System.{u, u} X)
    (hU : ∃ i, U i = Set.univ) :
    (fullCoverChainIso U A hU).hom = smallChainComplexInclusion U A := rfl

end FundamentalGroupoid.LocalCoefficients
