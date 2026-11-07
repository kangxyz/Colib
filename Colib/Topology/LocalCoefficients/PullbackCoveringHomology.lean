/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.IntegralChains
public import Colib.Topology.Covering.SingularSimplices
public import Colib.Topology.Covering.Pullback
public import Colib.Topology.LocalCoefficients.UniverseLift
public import Mathlib.Algebra.Homology.QuasiIso

/-!
Extracted from `Quillen/Topology/LocalCoefficients/PullbackCoveringHomology.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original coefficient modules,
monodromy, singular-chain arrows, and universe parameters are retained.

# Actual covering-fiber chains and the literal pullback projection

The coefficient module at a base point is the free integral module on the
actual fiber of the supplied covering, with its genuine covering monodromy.
A source simplex together with a point over its mapped first vertex lifts
uniquely to the literal matching-pair pullback. Forward transport from vertex
zero to vertex one is retained in the zeroth face; all simplicial restrictions
commute with the lift.

The resulting chain isomorphisms identify the original twisted arrow with
mathlib's original integral singular-chain arrow of the second pullback
projection. The existing same-universe UniverseLift comparison then transfers
quasi-isomorphism. No connectedness, fundamental-group bijectivity, universal
cover existence, or homotopy-fiber perfectness is a hypothesis or conclusion.
Mixed-universe application requires a separate comparison with the original
ULift maps and pullback model.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits Opposite
open scoped Simplicial
universe u

namespace FundamentalGroupoid.LocalCoefficients.PullbackCovering
variable {E B X : Type u} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace X]
  {q : E → B} (hq : IsCoveringMap q)

/-- The actual covering fibers freely span the coefficient modules; transport is monodromy. -/
def fiberSystem : System.{u, u} B where
  obj x := ModuleCat.of ℤ ({e : E // q e = x.as} →₀ ℤ)
  map p := ModuleCat.ofHom (Finsupp.lmapDomain ℤ ℤ (hq.monodromy p))
  map_id x := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro e z
    simp only [ModuleCat.hom_ofHom, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      ModuleCat.hom_id, LinearMap.id_coe, id_eq]
    change Finsupp.single (hq.monodromy (.refl x.as) e) z = Finsupp.single e z
    rw [hq.monodromy_refl]
    rfl
  map_comp p r := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro e z
    simp only [ModuleCat.hom_ofHom, ModuleCat.hom_comp, LinearMap.coe_comp,
      Function.comp_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    exact congrArg (fun e => Finsupp.single e z) (hq.monodromy_trans_apply p r e)

/-- An actual covering-fiber basis vector with its original integer coefficient. -/
def single {x : B} (e : {e : E // q e = x}) (z : ℤ) : fiber (fiberSystem hq) x :=
  Finsupp.single e z

/-- Transport along the actual path uses the actual covering monodromy endpoint. -/
@[simp] theorem transport_single {x y : B} (p : Path x y)
    (e : {e : E // q e = x}) (z : ℤ) :
    transport (fiberSystem hq) p (single hq e z) = single hq (hq.monodromy (.mk p) e) z :=
  Finsupp.mapDomain_single

/-- A simplex of the original source together with its actual target-cover fiber point. -/
abbrev FiberSimplex (f : C(X, B)) (n : SimplexCategory) :=
  Σ σ : SingularSimplex X n, {e : E // q e = f (σ (Convexity.StdSimplex.single 0))}

/-- The original source simplex is pushed forward without changing its chosen fiber point. -/
def mapSimplex (f : C(X, B)) {n : SimplexCategory} (s : FiberSimplex (q := q) f n) :
    IsCoveringMap.BasedSimplex q n := ⟨f.comp s.1, s.2⟩

/-- The coefficient at the first vertex is inserted into the original chain coproduct. -/
def generator (f : C(X, B)) {n : SimplexCategory} (s : FiberSimplex (q := q) f n) (z : ℤ) :
    chainModule (pullback f (fiberSystem hq)) n := chainInclusion (pullback f (fiberSystem hq)) s.1
      (single hq s.2 z)

/-- Flatten the coproduct of the actual free covering-fiber modules. -/
def basisHom (f : C(X, B)) (n : SimplexCategory) :
    chainModule (pullback f (fiberSystem hq)) n ⟶ ModuleCat.of ℤ (FiberSimplex (q := q) f n →₀ ℤ) :=
  Sigma.desc fun σ => ModuleCat.ofHom
    (Finsupp.lmapDomain ℤ ℤ (fun e => (⟨σ, e⟩ : FiberSimplex (q := q) f n)))

/-- Insert a finite combination of the actual simplex/fiber pairs into the original chains. -/
def basisInv (f : C(X, B)) (n : SimplexCategory) :
    ModuleCat.of ℤ (FiberSimplex (q := q) f n →₀ ℤ) ⟶ chainModule (pullback f (fiberSystem hq)) n :=
  ModuleCat.ofHom (Finsupp.lsum ℕ fun s =>
    (chainInclusion (pullback f (fiberSystem hq)) s.1).hom.comp (Finsupp.lsingle s.2))

@[simp] theorem basisHom_generator (f : C(X, B)) {n : SimplexCategory}
    (s : FiberSimplex (q := q) f n) (z : ℤ) :
    basisHom hq f n (generator hq f s z) = Finsupp.single s z := by
  rcases s with ⟨σ, e⟩
  change (chainInclusion (pullback f (fiberSystem hq)) σ ≫ basisHom hq f n)
    (Finsupp.single e z) = _
  rw [show chainInclusion (pullback f (fiberSystem hq)) σ ≫ basisHom hq f n =
    ModuleCat.ofHom (Finsupp.lmapDomain ℤ ℤ
      (fun e => (⟨σ, e⟩ : FiberSimplex (q := q) f n))) from Sigma.ι_comp_desc _ _]
  exact Finsupp.mapDomain_single

@[simp] theorem basisInv_single (f : C(X, B)) {n : SimplexCategory}
    (s : FiberSimplex (q := q) f n) (z : ℤ) :
    basisInv hq f n (Finsupp.single s z) = generator hq f s z := by
  exact Finsupp.lsum_single (S := ℕ) (R := ℤ) _ _ _

/-- The actual chain coproduct is freely generated by the original simplex/fiber pairs. -/
def basisIso (f : C(X, B)) (n : SimplexCategory) :
    chainModule (pullback f (fiberSystem hq)) n ≅
      ModuleCat.of ℤ (FiberSimplex (q := q) f n →₀ ℤ) where
  hom := basisHom hq f n
  inv := basisInv hq f n
  hom_inv_id := by
    apply Sigma.hom_ext
    intro σ
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro e z
    change basisInv hq f n (basisHom hq f n (generator hq f ⟨σ, e⟩ z)) =
      generator hq f ⟨σ, e⟩ z
    rw [basisHom_generator, basisInv_single]
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro s z
    change basisHom hq f n (basisInv hq f n (Finsupp.single s z)) = _
    rw [basisInv_single, basisHom_generator]
    rfl

/-- Restriction transports the chosen point along the image of the original first-vertex path. -/
def restrict (f : C(X, B)) {m n : SimplexCategory}
    (s : FiberSimplex (q := q) f n) (α : m ⟶ n) : FiberSimplex (q := q) f m :=
  ⟨restrictSimplex s.1 α,
    IsCoveringMap.simplexTransport hq (f.comp s.1) (Convexity.StdSimplex.single 0)
      (Convexity.StdSimplex.map α (Convexity.StdSimplex.single 0)) s.2⟩

/-- The original differential's face-zero convention is the forward first-vertex transport. -/
@[simp] theorem chainMap_generator (f : C(X, B)) {m n : SimplexCategory}
    (s : FiberSimplex (q := q) f n) (α : m ⟶ n) (z : ℤ) :
    chainMap (pullback f (fiberSystem hq)) α (generator hq f s z) =
      generator hq f (restrict hq f s α) z := by
  change (chainInclusion (pullback f (fiberSystem hq)) s.1 ≫
    chainMap (pullback f (fiberSystem hq)) α) (single hq s.2 z) = _
  rw [chainInclusion_chainMap]
  change chainInclusion (pullback f (fiberSystem hq)) (restrictSimplex s.1 α)
    (transport (fiberSystem hq) (((PathConnectedSpace.somePath (Convexity.StdSimplex.single 0)
      (Convexity.StdSimplex.map α (Convexity.StdSimplex.single 0))).map
        s.1.continuous).map f.continuous)
        (single hq s.2 z)) = _
  rw [transport_single]
  rfl

end FundamentalGroupoid.LocalCoefficients.PullbackCovering

namespace FundamentalGroupoid.LocalCoefficients.PullbackCovering
variable {E B X : Type u} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace X]
  {q : E → B} (hq : IsCoveringMap q) (f : C(X, B))

/-- The literal matching-pair subtype, with its original product/subspace topology. -/
abbrev Pullback := Topology.Covering.Pullback.Space f q

/-- The original first projection of the literal pullback. -/
def pullbackProjection : C(Pullback (q := q) f, X) :=
  Topology.Covering.Pullback.projection f q

/-- The original second projection of the literal pullback. -/
def pullbackLift : C(Pullback (q := q) f, E) :=
  Topology.Covering.Pullback.lift f q

/-- Its fiber is exactly the original covering fiber over the mapped point. -/
def pullbackFiberEquiv (x : X) :
    {z : Pullback (q := q) f // pullbackProjection f z = x} ≃ {e : E // q e = f x} where
  toFun z := ⟨z.1.1.2, z.1.2.symm.trans (congrArg f z.2)⟩
  invFun e := ⟨⟨(x, e.1), e.2.symm⟩, rfl⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext z.2.symm rfl
  right_inv e := rfl

/-- Lift the composite simplex in the supplied cover and retain the original source simplex. -/
def pullbackSimplexLift {n : SimplexCategory} (s : FiberSimplex (q := q) f n) :
    SingularSimplex (Pullback (q := q) f) n where
  toFun t := ⟨(s.1 t, IsCoveringMap.lift hq (f.comp s.1) s.2.1 s.2.2 t),
    (ContinuousMap.congr_fun (IsCoveringMap.projection_lift hq (f.comp s.1) s.2.1 s.2.2) t).symm⟩
  continuous_toFun := Continuous.subtype_mk
    (s.1.continuous.prodMk (IsCoveringMap.lift hq (f.comp s.1) s.2.1 s.2.2).continuous) _

/-- The first coordinate is exactly the original simplex. -/
@[simp] theorem pullbackSimplexLift_projection {n : SimplexCategory}
    (s : FiberSimplex (q := q) f n) :
    (pullbackProjection f).comp (pullbackSimplexLift hq f s) = s.1 := rfl

/-- The second coordinate is exactly the unique original covering lift. -/
@[simp] theorem pullbackSimplexLift_second {n : SimplexCategory}
    (s : FiberSimplex (q := q) f n) :
    (pullbackLift f).comp (pullbackSimplexLift hq f s) =
      IsCoveringMap.lift hq (f.comp s.1) s.2.1 s.2.2 := rfl

/-- An actual pullback simplex is equivalent to a source simplex and its chosen covering point. -/
def pullbackSimplexEquiv (n : SimplexCategory) :
    SingularSimplex (Pullback (q := q) f) n ≃ FiberSimplex (q := q) f n where
  toFun τ := ⟨(pullbackProjection f).comp τ,
    ⟨(τ (Convexity.StdSimplex.single 0)).1.2, (τ (Convexity.StdSimplex.single 0)).2.symm⟩⟩
  invFun s := pullbackSimplexLift hq f s
  left_inv τ := by
    have h : (pullbackLift f).comp τ =
        IsCoveringMap.lift hq (f.comp ((pullbackProjection f).comp τ))
          (τ (Convexity.StdSimplex.single 0)).1.2 (τ (Convexity.StdSimplex.single 0)).2.symm := by
      apply IsCoveringMap.eq_lift hq
      · ext t
        exact (τ t).2.symm
      · rfl
    apply ContinuousMap.ext
    intro t
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (ContinuousMap.congr_fun h t).symm
  right_inv s := by
    rcases s with ⟨σ, e, he⟩
    exact congrArg (fun e : {e : E // q e = f (σ (Convexity.StdSimplex.single 0))} =>
      (⟨σ, e⟩ : FiberSimplex (q := q) f n))
        (Subtype.ext (IsCoveringMap.lift_vertex hq (f.comp σ) e he))

/-- Restriction of a literal pullback lift transports the covering point
in the forward direction. -/
theorem pullbackSimplexLift_restrict {m n : SimplexCategory}
    (s : FiberSimplex (q := q) f n) (α : m ⟶ n) :
    pullbackSimplexLift hq f (restrict hq f s α) =
      restrictSimplex (pullbackSimplexLift hq f s) α := by
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact ContinuousMap.congr_fun (IsCoveringMap.lift_restrict hq (mapSimplex f s) α) t

end FundamentalGroupoid.LocalCoefficients.PullbackCovering

namespace FundamentalGroupoid.LocalCoefficients.PullbackCovering
variable {E B X : Type u} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace X]
  {q : E → B} (hq : IsCoveringMap q) (f : C(X, B))

/-- The target-cover degreewise comparison uses the unique original simplex lift. -/
def coveringModuleIso (n : SimplexCategory) :
    chainModule (fiberSystem hq) n ≅ chainModule (constant E integralCoefficients) n :=
  basisIso hq (ContinuousMap.id B) n ≪≫
    (Finsupp.mapDomain.linearEquiv ℤ ℤ (IsCoveringMap.simplexEquiv hq n).symm).toModuleIso ≪≫
      (integralBasisIso n).symm

/-- The original target generator is sent to its unique lifted simplex, retaining its integer. -/
@[simp] theorem coveringModuleIso_generator {n : SimplexCategory}
    (s : IsCoveringMap.BasedSimplex q n) (z : ℤ) :
    (coveringModuleIso hq n).hom (generator hq (ContinuousMap.id B) s z) =
      integralChainGenerator ((IsCoveringMap.simplexEquiv hq n).symm s) z := by
  change integralBasisInv n (Finsupp.mapDomain (IsCoveringMap.simplexEquiv hq n).symm
    (basisHom hq (ContinuousMap.id B) n (generator hq (ContinuousMap.id B) s z))) = _
  rw [basisHom_generator, Finsupp.mapDomain_single, integralBasisInv_single]

/-- The actual covering comparison commutes with every original face and degeneracy. -/
@[reassoc] theorem coveringModuleIso_naturality {m n : SimplexCategory} (α : m ⟶ n) :
    chainMap (fiberSystem hq) α ≫ (coveringModuleIso hq m).hom =
      (coveringModuleIso hq n).hom ≫ chainMap (constant E integralCoefficients) α := by
  apply Sigma.hom_ext
  intro σ
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro e z
  change (coveringModuleIso hq m).hom
    (chainMap (pullback (ContinuousMap.id B) (fiberSystem hq)) α
      (generator hq (ContinuousMap.id B) ⟨σ, e⟩ z)) =
    chainMap (constant E integralCoefficients) α
      ((coveringModuleIso hq n).hom (generator hq (ContinuousMap.id B) ⟨σ, e⟩ z))
  simp only [chainMap_generator, coveringModuleIso_generator, chainMap_integralGenerator]
  exact congrArg (fun τ => integralChainGenerator τ z)
    (IsCoveringMap.lift_restrict hq ⟨σ, e⟩ α)

/-- The actual covering comparison is a simplicial-module isomorphism without any SC hypothesis. -/
def coveringSimplicialIso :
    simplicialModule (fiberSystem hq) ≅ simplicialModule (constant E integralCoefficients) :=
  NatIso.ofComponents (fun n => coveringModuleIso hq n.unop)
    (by intro n m α; exact coveringModuleIso_naturality hq α.unop)

/-- The original free-fiber chains equal the actual constant chains of the covering space. -/
def coveringConstantChainIso :
    singularChainComplex (fiberSystem hq) ≅
      singularChainComplex (constant E integralCoefficients) :=
  (AlgebraicTopology.alternatingFaceMapComplex _).mapIso (coveringSimplicialIso hq)

/-- The comparison lands in mathlib's original integral singular-chain complex. -/
def coveringChainIso :
    singularChainComplex (fiberSystem hq) ≅
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj
        integralCoefficients).obj (TopCat.of E) :=
  coveringConstantChainIso hq ≪≫ constantChainComplexIso integralCoefficients

/-- The source degreewise comparison lifts into the literal pullback subtype. -/
def pullbackModuleIso (n : SimplexCategory) :
    chainModule (pullback f (fiberSystem hq)) n ≅
      chainModule (constant (Pullback (q := q) f) integralCoefficients) n :=
  basisIso hq f n ≪≫
    (Finsupp.mapDomain.linearEquiv ℤ ℤ (pullbackSimplexEquiv hq f n).symm).toModuleIso ≪≫
      (integralBasisIso n).symm

/-- The original source generator is sent to the actual matching-pair simplex. -/
@[simp] theorem pullbackModuleIso_generator {n : SimplexCategory}
    (s : FiberSimplex (q := q) f n) (z : ℤ) :
    (pullbackModuleIso hq f n).hom (generator hq f s z) =
      integralChainGenerator (pullbackSimplexLift hq f s) z := by
  change integralBasisInv n (Finsupp.mapDomain (pullbackSimplexEquiv hq f n).symm
    (basisHom hq f n (generator hq f s z))) = _
  rw [basisHom_generator, Finsupp.mapDomain_single, integralBasisInv_single]
  rfl

/-- The source comparison commutes with every actual restriction, including zeroth faces. -/
@[reassoc] theorem pullbackModuleIso_naturality {m n : SimplexCategory} (α : m ⟶ n) :
    chainMap (pullback f (fiberSystem hq)) α ≫ (pullbackModuleIso hq f m).hom =
      (pullbackModuleIso hq f n).hom ≫
        chainMap (constant (Pullback (q := q) f) integralCoefficients) α := by
  apply Sigma.hom_ext
  intro σ
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro e z
  change (pullbackModuleIso hq f m).hom
    (chainMap (pullback f (fiberSystem hq)) α (generator hq f ⟨σ, e⟩ z)) =
    chainMap (constant (Pullback (q := q) f) integralCoefficients) α
      ((pullbackModuleIso hq f n).hom (generator hq f ⟨σ, e⟩ z))
  simp only [chainMap_generator, pullbackModuleIso_generator, chainMap_integralGenerator]
  exact congrArg (fun τ => integralChainGenerator τ z) (pullbackSimplexLift_restrict hq f ⟨σ, e⟩ α)

/-- The entire pullback comparison is an isomorphism of the original simplicial modules. -/
def pullbackSimplicialIso :
    simplicialModule (pullback f (fiberSystem hq)) ≅
      simplicialModule (constant (Pullback (q := q) f) integralCoefficients) :=
  NatIso.ofComponents (fun n => pullbackModuleIso hq f n.unop)
    (by intro n m α; exact pullbackModuleIso_naturality hq f α.unop)

/-- The actual pulled-back fiber system identifies with constant chains of the literal pullback. -/
def pullbackConstantChainIso :
    singularChainComplex (pullback f (fiberSystem hq)) ≅
      singularChainComplex (constant (Pullback (q := q) f) integralCoefficients) :=
  (AlgebraicTopology.alternatingFaceMapComplex _).mapIso (pullbackSimplicialIso hq f)

/-- The source comparison lands in the original integral singular chains of the literal pullback. -/
def pullbackChainIso :
    singularChainComplex (pullback f (fiberSystem hq)) ≅
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj
        integralCoefficients).obj (TopCat.of (Pullback (q := q) f)) :=
  pullbackConstantChainIso hq f ≪≫ constantChainComplexIso integralCoefficients

/-- The original spatial pushforward retains the actual chosen fiber point. -/
@[simp] theorem pushforward_generator {n : SimplexCategory}
    (s : FiberSimplex (q := q) f n) (z : ℤ) :
    pushforwardModuleMap f (fiberSystem hq) n (generator hq f s z) =
      generator hq (ContinuousMap.id B) (mapSimplex f s) z := by
  change (chainInclusion (pullback f (fiberSystem hq)) s.1 ≫
    pushforwardModuleMap f (fiberSystem hq) n) (single hq s.2 z) = _
  rw [chainInclusion_pushforwardModuleMap]
  rfl

/-- The actual comparison square has the literal second pullback projection as its lower map. -/
@[reassoc] theorem moduleIso_map (n : SimplexCategory) :
    pushforwardModuleMap f (fiberSystem hq) n ≫ (coveringModuleIso hq n).hom =
      (pullbackModuleIso hq f n).hom ≫
        pushforwardModuleMap (pullbackLift f) (constant E integralCoefficients) n := by
  apply Sigma.hom_ext
  intro σ
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro e z
  change (coveringModuleIso hq n).hom
    (pushforwardModuleMap f (fiberSystem hq) n (generator hq f ⟨σ, e⟩ z)) =
      pushforwardModuleMap (pullbackLift f) (constant E integralCoefficients) n
        ((pullbackModuleIso hq f n).hom (generator hq f ⟨σ, e⟩ z))
  rw [pushforward_generator, coveringModuleIso_generator, pullbackModuleIso_generator,
    pushforwardModuleMap_integralGenerator]
  rfl

/-- The original-map square holds already for simplicial modules. -/
@[reassoc] theorem simplicialIso_map :
    pushforwardSimplicialMap f (fiberSystem hq) ≫ (coveringSimplicialIso hq).hom =
      (pullbackSimplicialIso hq f).hom ≫
        pushforwardSimplicialMap (pullbackLift f) (constant E integralCoefficients) := by
  ext n : 1
  exact moduleIso_map hq f n.unop

/-- Alternating faces preserve the exact original chain-map square. -/
@[reassoc] theorem constantChainIso_map :
    pushforwardChainMap f (fiberSystem hq) ≫ (coveringConstantChainIso hq).hom =
      (pullbackConstantChainIso hq f).hom ≫
        pushforwardChainMap (pullbackLift f) (constant E integralCoefficients) := by
  have h := congrArg (fun η => (AlgebraicTopology.alternatingFaceMapComplex
    (ModuleCat.{u} ℤ)).map η) (simplicialIso_map hq f)
  simpa only [pushforwardChainMap, coveringConstantChainIso, pullbackConstantChainIso,
    Functor.map_comp, Functor.mapIso_hom] using h

/-- Standard reindexing retains mathlib's actual singular-chain map of the original projection. -/
@[reassoc] theorem chainIso_map :
    pushforwardChainMap f (fiberSystem hq) ≫ (coveringChainIso hq).hom =
      (pullbackChainIso hq f).hom ≫
        ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj
          integralCoefficients).map (TopCat.ofHom (pullbackLift f)) := by
  simp only [coveringChainIso, pullbackChainIso, Iso.trans_hom, ← Category.assoc]
  rw [constantChainIso_map hq f]
  simp only [Category.assoc, constantChainComplexIso_naturality]

end FundamentalGroupoid.LocalCoefficients.PullbackCovering

namespace FundamentalGroupoid.LocalCoefficients.PullbackCovering
variable {E B X : Type u} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace X]
  {q : E → B} (hq : IsCoveringMap q) (f : C(X, B))

/-- The zeroth face transports from the original vertex zero to vertex one in the base. -/
theorem restrict_firstFace_point {n : ℕ} (s : FiberSimplex (q := q) f ⦋n + 1⦌) :
    (restrict hq f s (SimplexCategory.δ 0)).2.1 =
      (IsCoveringMap.simplexTransport hq (f.comp s.1) (Convexity.StdSimplex.single 0)
        (Convexity.StdSimplex.single 1) s.2).1 :=
  IsCoveringMap.restrict_firstFace_point hq (mapSimplex f s)

/-- Every later face retains the actual original point of the covering fiber. -/
theorem restrict_laterFace_point {n : ℕ} (s : FiberSimplex (q := q) f ⦋n + 1⦌)
    (i : Fin (n + 1)) : (restrict hq f s (SimplexCategory.δ i.succ)).2.1 = s.2.1 :=
  IsCoveringMap.restrict_laterFace_point hq (mapSimplex f s) i

/-- The original twisted arrow for the actual covering-fiber system is isomorphic to
mathlib's integral chain arrow of the literal second pullback projection. -/
def singularArrowIso :
    Arrow.mk (pushforwardChainMap f (fiberSystem hq)) ≅
      Arrow.mk (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj
        integralCoefficients).map (TopCat.ofHom (pullbackLift (q := q) f))) :=
  Arrow.isoMk (pullbackChainIso hq f) (coveringChainIso hq) (chainIso_map hq f).symm

/-- The existing UniverseLift comparison retains both original maps in the same universe. -/
def universeLiftSingularArrowIso :
    Arrow.mk (UniverseLift.chainMap.{u, u, u} f (fiberSystem hq)) ≅
      Arrow.mk (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj
        integralCoefficients).map (TopCat.ofHom (pullbackLift (q := q) f))) :=
  (Arrow.isoMk
    (f := Arrow.mk (UniverseLift.chainMap.{u, u, u} f (fiberSystem hq)))
    (g := Arrow.mk (pushforwardChainMap f (fiberSystem hq)))
    (UniverseLift.chainComparisonIso (pullback f (fiberSystem hq)))
    (UniverseLift.chainComparisonIso (fiberSystem hq))
    (UniverseLift.chainComparisonIso_naturality f (fiberSystem hq)).symm) ≪≫
      singularArrowIso hq f

include hq in
/-- Quasi-isomorphism transfers through the actual original chain-map square.
There is no connectedness or fundamental-group bijectivity hypothesis. -/
theorem pullback_quasiIso_iff :
    QuasiIso (UniverseLift.chainMap.{u, u, u} f (fiberSystem hq)) ↔
      QuasiIso (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj
        integralCoefficients).map (TopCat.ofHom (pullbackLift (q := q) f))) :=
  quasiIso_iff_of_arrow_mk_iso _ _ (universeLiftSingularArrowIso hq f)

include hq in
/-- Testing all actual target systems includes the free module on the actual covering fibers.
Therefore the ORIGINAL second projection of the literal pullback is an integral homology
equivalence, without assuming that either covering total space is simply connected. -/
theorem pullback_singular_quasiIso_of_all_localCoefficients
    (hH : ∀ A : System.{u, u} B, QuasiIso (UniverseLift.chainMap.{u, u, u} f A)) :
    QuasiIso (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj
      integralCoefficients).map (TopCat.ofHom (pullbackLift (q := q) f))) :=
  (pullback_quasiIso_iff hq f).mp (hH (fiberSystem hq))

end FundamentalGroupoid.LocalCoefficients.PullbackCovering
