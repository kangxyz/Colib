/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.PullbackCoveringHomology

/-!
Extracted from the pinned source
`Quillen/Topology/LocalCoefficients/PullbackCoveringHomologyUniverseLift.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original coefficient modules,
monodromy, singular-chain arrows, and universe parameters are retained.

# Original pullback-cover chains with a lower-universe source

Only the source space is lifted to the common target universe. The original
UniverseLift coefficient-down map and target chain comparison identify the
original mixed-universe twisted arrow with the same-universe spatial arrow.
The existing covering-fiber comparison applies to that arrow. An explicit
homeomorphism lifts the source coordinate of each matching pair and leaves
the covering coordinate unchanged, so the resulting ordinary chain arrow is
exactly the original second projection of the shared literal pullback.

The source is in Type u and the target and supplied cover in Type (max u v).
The successor-universe specialization retains ModuleCat.{u+1} integers and the
original ULift integral coefficient object. There is no connectedness,
fundamental-group bijectivity, or covering-existence premise. No homotopy-fiber
perfectness statement is made.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits Opposite
open scoped Simplicial
universe u v

namespace FundamentalGroupoid.LocalCoefficients.PullbackCoveringUniverseLift
variable {X : Type u} {B : Type (max u v)} [TopologicalSpace X] [TopologicalSpace B]
  (f : C(X, B))

/-- The original map with only its source lifted to the target's common universe. -/
def sourceLift : C(ULift.{max u v} X, B) :=
  f.comp (UniverseLift.down.{u, max u v} X)

/-- The original source coefficient lift has the actual coefficient-down isomorphism. -/
def sourceCoefficientIso (A : System.{max u v, max u v} B) :
    UniverseLift.system.{u, max u v, max u v} (pullback f A) ≅
      pullback (sourceLift f) A :=
  NatIso.ofComponents
    (fun x => (UniverseLift.fiberEquiv (pullback f A) x.as).toModuleIso) (by
      intro x y p
      obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective p
      ext a
      rfl)

/-- The coefficient-down comparison is a genuine chain isomorphism on the original source. -/
def sourceChainIso (A : System.{max u v, max u v} B) :
    UniverseLift.chainComplex.{u, max u v, max u v} (pullback f A) ≅
      singularChainComplex (pullback (sourceLift f) A) :=
  coefficientChainIso (sourceCoefficientIso f A)

/-- The original mixed-universe chain arrow becomes the ordinary spatial arrow of the
source-lifted map, with the original target chain comparison and the displayed
source coefficients. -/
@[reassoc] theorem sourceChainIso_square (A : System.{max u v, max u v} B) :
    UniverseLift.chainMap.{u, max u v, max u v} f A ≫
        (UniverseLift.chainComparisonIso A).hom =
      (sourceChainIso f A).hom ≫ pushforwardChainMap (sourceLift f) A := by
  ext n : 1
  apply Sigma.hom_ext
  intro σ
  change chainInclusion (UniverseLift.system.{u, max u v, max u v} (pullback f A)) σ ≫
      ((UniverseLift.chainMap.{u, max u v, max u v} f A).f n ≫
        (UniverseLift.chainComparisonIso A).hom.f n) =
    chainInclusion (UniverseLift.system.{u, max u v, max u v} (pullback f A)) σ ≫
      ((sourceChainIso f A).hom.f n ≫ (pushforwardChainMap (sourceLift f) A).f n)
  rw [← Category.assoc, UniverseLift.chainInclusion_chainMap]
  erw [UniverseLift.chainInclusion_chainComparisonIso]
  rw [← Category.assoc]
  change _ = (chainInclusion (UniverseLift.system.{u, max u v, max u v} (pullback f A)) σ ≫
    coefficientModuleMap (sourceCoefficientIso f A).hom ⦋n⦌) ≫
      pushforwardModuleMap (sourceLift f) A ⦋n⦌
  rw [chainInclusion_coefficientModuleMap, Category.assoc, chainInclusion_pushforwardModuleMap]
  rfl

/-- The displayed square is an isomorphism of the original mixed and source-lifted arrows. -/
def sourceLiftArrowIso (A : System.{max u v, max u v} B) :
    Arrow.mk (UniverseLift.chainMap.{u, max u v, max u v} f A) ≅
      Arrow.mk (pushforwardChainMap (sourceLift f) A) :=
  Arrow.isoMk (sourceChainIso f A) (UniverseLift.chainComparisonIso A)
    (sourceChainIso_square f A).symm

end FundamentalGroupoid.LocalCoefficients.PullbackCoveringUniverseLift

namespace FundamentalGroupoid.LocalCoefficients.PullbackCoveringUniverseLift
variable {X : Type u} {B E : Type (max u v)}
  [TopologicalSpace X] [TopologicalSpace B] [TopologicalSpace E]
  {q : E → B} (f : C(X, B))

/-- The original literal pullback, with a possibly lower-universe first coordinate. -/
abbrev MixedPullback := Topology.Covering.Pullback.Space f q

/-- The original second projection of that actual mixed-universe subtype. -/
def mixedPullbackLift : C(MixedPullback (q := q) f, E) :=
  Topology.Covering.Pullback.lift f q

/-- Lift only the first coordinate of each actual matching pair. -/
def pullbackSourceHomeomorph :
    MixedPullback (q := q) f ≃ₜ PullbackCovering.Pullback (q := q) (sourceLift f) where
  toFun z := ⟨(ULift.up z.1.1, z.1.2), z.2⟩
  invFun z := ⟨(z.1.1.down, z.1.2), z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The homeomorphism leaves the actual covering point, and hence k, unchanged. -/
@[simp] theorem pullbackSourceHomeomorph_second (z : MixedPullback (q := q) f) :
    PullbackCovering.pullbackLift (sourceLift f) (pullbackSourceHomeomorph f z) =
      mixedPullbackLift f z := rfl

/-- The original projection square is a literal equality of continuous maps. -/
theorem pullbackSourceHomeomorph_square :
    (PullbackCovering.pullbackLift (sourceLift f)).comp
      ⟨pullbackSourceHomeomorph (q := q) f,
        (pullbackSourceHomeomorph f).continuous⟩ = mixedPullbackLift f := rfl

/-- The actual integral singular-chain arrows are isomorphic through that homeomorphism. -/
def projectionArrowIso :
    Arrow.mk (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{max u v} ℤ)).obj
      integralCoefficients).map (TopCat.ofHom (mixedPullbackLift (q := q) f))) ≅
    Arrow.mk (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{max u v} ℤ)).obj
      integralCoefficients).map (TopCat.ofHom (PullbackCovering.pullbackLift
        (q := q) (sourceLift f)))) := by
  let S := (AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{max u v} ℤ)).obj
    integralCoefficients
  refine Arrow.isoMk (S.mapIso (TopCat.isoOfHomeo (pullbackSourceHomeomorph (q := q) f)))
    (Iso.refl _) ?_
  change S.map (TopCat.ofHom ⟨pullbackSourceHomeomorph (q := q) f,
        (pullbackSourceHomeomorph f).continuous⟩) ≫
    S.map (TopCat.ofHom (PullbackCovering.pullbackLift (q := q) (sourceLift f))) =
      S.map (TopCat.ofHom (mixedPullbackLift (q := q) f)) ≫ 𝟙 _
  rw [Category.comp_id, ← Functor.map_comp]
  rfl

end FundamentalGroupoid.LocalCoefficients.PullbackCoveringUniverseLift

namespace FundamentalGroupoid.LocalCoefficients.PullbackCoveringUniverseLift
variable {X : Type u} {B E : Type (max u v)}
  [TopologicalSpace X] [TopologicalSpace B] [TopologicalSpace E]
  {q : E → B} (hq : IsCoveringMap q) (f : C(X, B))

/-- The original mixed-universe twisted arrow for the actual covering-fiber system
is isomorphic to the original integral singular-chain arrow of the shared literal projection. -/
def mixedSingularArrowIso :
    Arrow.mk (UniverseLift.chainMap.{u, max u v, max u v} f (PullbackCovering.fiberSystem hq)) ≅
      Arrow.mk (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{max u v} ℤ)).obj
        integralCoefficients).map (TopCat.ofHom (Topology.Covering.Pullback.lift f q))) :=
  (sourceLiftArrowIso f (PullbackCovering.fiberSystem hq)) ≪≫
    PullbackCovering.singularArrowIso hq (sourceLift f) ≪≫ (projectionArrowIso f).symm

/-- Applying native homology to the actual chain-arrow isomorphism retains the literal
second projection and the covering-fiber local system in every degree. -/
def mixedHomologyArrowIso (n : ℕ) :
    Arrow.mk (UniverseLift.homologyMap.{u, max u v, max u v} f
      (PullbackCovering.fiberSystem hq) n) ≅
      Arrow.mk (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{max u v} ℤ) n).obj
        integralCoefficients).map (TopCat.ofHom (Topology.Covering.Pullback.lift f q))) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{max u v} ℤ)
    (ComplexShape.down ℕ) n).mapArrow.mapIso (mixedSingularArrowIso hq f)

/-- The degree-two comparison for a lower-universe source uses exactly the successor-universe
integral coefficient object and the original second projection of the literal pullback.
No homology isomorphism of the original map is assumed here. -/
def successorHomologyTwoArrowIso
    {S : Type u} {T V : Type (u + 1)}
    [TopologicalSpace S] [TopologicalSpace T] [TopologicalSpace V]
    (g : C(S, T)) {p : V → T} (hp : IsCoveringMap p) :
    Arrow.mk (UniverseLift.homologyMap.{u, u + 1, u + 1} g
      (PullbackCovering.fiberSystem hp) 2) ≅
      Arrow.mk (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u + 1} ℤ) 2).obj
        (ModuleCat.of ℤ (ULift.{u + 1} ℤ))).map
          (TopCat.ofHom (Topology.Covering.Pullback.lift g p))) :=
  mixedHomologyArrowIso.{u, u + 1} hp g 2

include hq in
/-- The one actual covering-fiber system detects precisely the original integral map
of the literal mixed-universe pullback. No source simple-connectedness is used. -/
theorem mixed_quasiIso_iff :
    QuasiIso (UniverseLift.chainMap.{u, max u v, max u v} f (PullbackCovering.fiberSystem hq)) ↔
      QuasiIso (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{max u v} ℤ)).obj
        integralCoefficients).map (TopCat.ofHom (Topology.Covering.Pullback.lift f q))) :=
  quasiIso_iff_of_arrow_mk_iso _ _ (mixedSingularArrowIso hq f)

include hq in
/-- All actual target systems include the actual covering-fiber system, so the original
integral second-projection map is a quasi-isomorphism even when the source universe is smaller. -/
theorem mixed_singular_quasiIso_of_all_localCoefficients
    (hH : ∀ A : System.{max u v, max u v} B,
      QuasiIso (UniverseLift.chainMap.{u, max u v, max u v} f A)) :
    QuasiIso (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{max u v} ℤ)).obj
      integralCoefficients).map (TopCat.ofHom (Topology.Covering.Pullback.lift f q))) :=
  (mixed_quasiIso_iff hq f).mp (hH (PullbackCovering.fiberSystem hq))

/-- The concrete successor-universe direction needed by the original stable zero map. -/
theorem successor_singular_quasiIso_of_all_localCoefficients
    {S : Type u} {T V : Type (u + 1)}
    [TopologicalSpace S] [TopologicalSpace T] [TopologicalSpace V]
    (g : C(S, T)) {p : V → T} (hp : IsCoveringMap p)
    (hH : ∀ A : System.{u + 1, u + 1} T,
      QuasiIso (UniverseLift.chainMap.{u, u + 1, u + 1} g A)) :
    QuasiIso (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u + 1} ℤ)).obj
      integralCoefficients).map (TopCat.ofHom (Topology.Covering.Pullback.lift g p))) :=
  mixed_singular_quasiIso_of_all_localCoefficients.{u, u + 1} hp g hH

end FundamentalGroupoid.LocalCoefficients.PullbackCoveringUniverseLift
