/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.Homology
public import Mathlib.Algebra.Category.ModuleCat.Ulift

/-!
Extracted from `Quillen/Topology/LocalCoefficients/UniverseLift.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original coefficient modules,
monodromy, singular-chain arrows, and universe parameters are retained.

# Local-coefficient chains across arbitrary universes

Both spaces and every actual coefficient module are lifted to a common universe.
The resulting chain map is the existing singular-chain map of the lifted continuous
map. Its simplex formula retains the original continuous map and all monodromy.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits
open scoped Simplicial

universe u v w

namespace FundamentalGroupoid.LocalCoefficients.UniverseLift

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The genuine projection homeomorphism, regarded as a continuous map. -/
def down (X : Type u) [TopologicalSpace X] : C(ULift.{v} X, X) :=
  ⟨ULift.down, continuous_uliftDown⟩

/-- The inverse of the projection homeomorphism. -/
def up (X : Type u) [TopologicalSpace X] : C(X, ULift.{v} X) :=
  ⟨ULift.up, continuous_uliftUp⟩

/-- The original continuous map, conjugated by the genuine lift homeomorphisms. -/
def map (f : C(X, Y)) : C(ULift.{max v w} X, ULift.{max u w} Y) :=
  (up Y).comp (f.comp (down X))

@[simp]
theorem map_apply (f : C(X, Y)) (x : ULift.{max v w} X) :
    map.{u, v, w} f x = ULift.up (f x.down) := rfl

/-- Lift each actual coefficient module after pulling back along the homeomorphism. -/
def system (A : System.{u, v} X) :
    System.{max u v w, max u v w} (ULift.{max v w} X) :=
  pullback (down X) A ⋙ ModuleCat.uliftFunctor.{max u w, v} ℤ

/-- Fibers retain precisely the original elements, with a universe lift. -/
def fiberEquiv (A : System.{u, v} X) (x : ULift.{max v w} X) :
    fiber (system.{u, v, w} A) x ≃ₗ[ℤ] fiber A x.down :=
  ULift.moduleEquiv

/-- Every original monodromy operator is retained on the lifted coefficients. -/
theorem transport_apply (A : System.{u, v} X) {x y : ULift.{max v w} X}
    (p : Path x y) (a : fiber (system.{u, v, w} A) x) :
    (transport (system.{u, v, w} A) p a).down =
      transport A (p.map continuous_uliftDown) a.down := rfl

/-- The original and lifted singular simplices are in genuine bijection. -/
def simplexEquiv (X : Type u) [TopologicalSpace X] (n : SimplexCategory) :
    SingularSimplex (ULift.{v} X) n ≃ SingularSimplex X n where
  toFun σ := (down X).comp σ
  invFun σ := (up X).comp σ
  left_inv σ := by ext x; rfl
  right_inv σ := by ext x; rfl

/-- The simplex bijection commutes with every actual simplicial restriction. -/
@[simp]
theorem simplexEquiv_restrict {m n : SimplexCategory}
    (σ : SingularSimplex (ULift.{v} X) n) (α : m ⟶ n) :
    simplexEquiv X m (restrictSimplex σ α) =
      restrictSimplex (simplexEquiv X n σ) α := rfl

/-- Postcomposition is exactly postcomposition by the original map under the bijections. -/
@[simp]
theorem simplexEquiv_map (f : C(X, Y)) {n : SimplexCategory}
    (σ : SingularSimplex (ULift.{max v w} X) n) :
    simplexEquiv Y n ((map.{u, v, w} f).comp σ) =
      f.comp (simplexEquiv X n σ) := rfl

/-- Lifting and pulling back have identity coefficient components. -/
def pullbackIso (f : C(X, Y)) (A : System.{v, w} Y) :
    system.{u, w, v} (pullback f A) ≅
      pullback (map.{u, v, w} f) (system.{v, w, u} A) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro x y p
    obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective p
    simp only [Iso.refl_hom]
    rfl)

/-- Actual twisted chains for a space and coefficients of unrelated universes. -/
def chainComplex (A : System.{u, v} X) :
    ChainComplex (ModuleCat.{max u v w} ℤ) ℕ :=
  singularChainComplex (system.{u, v, w} A)

/-- Homology of the actual lifted twisted-chain complex. -/
def homology (A : System.{u, v} X) (n : ℕ) : ModuleCat.{max u v w} ℤ :=
  (chainComplex.{u, v, w} A).homology n

/-- The genuine chain map of an arbitrary-universe continuous map and target local system. -/
def chainMap (f : C(X, Y)) (A : System.{v, w} Y) :
    chainComplex.{u, w, v} (pullback f A) ⟶ chainComplex.{v, w, u} A :=
  (coefficientChainIso (pullbackIso f A)).hom ≫
    pushforwardChainMap (map.{u, v, w} f) (system.{v, w, u} A)

/-- Its action on homology is induced by the preceding genuine chain map. -/
def homologyMap (f : C(X, Y)) (A : System.{v, w} Y) (n : ℕ) :
    homology.{u, w, v} (pullback f A) n ⟶ homology.{v, w, u} A n :=
  (HomologicalComplex.homologyFunctor _ _ n).map (chainMap f A)

/-- The chain map on every summand sends the lifted simplex to the lift of its
original composite and leaves its actual coefficient unchanged. -/
@[reassoc]
theorem chainInclusion_chainMap (f : C(X, Y)) (A : System.{v, w} Y)
    {n : ℕ} (σ : SingularSimplex (ULift.{max v w} X) ⦋n⦌) :
    chainInclusion (system.{u, w, v} (pullback f A)) σ ≫ (chainMap f A).f n =
      chainInclusion (system.{v, w, u} A) ((map.{u, v, w} f).comp σ) := by
  simp [chainMap, coefficientChainIso, coefficientChainFunctor, coefficientChainMap,
    coefficientSimplicialMap, coefficientModuleMap, pullbackIso, pushforwardChainMap,
    pushforwardSimplicialMap, pushforwardModuleMap, chainInclusion]

/-- The comparison to the usual homology map of the genuine lifted continuous map. -/
theorem homologyMap_eq (f : C(X, Y)) (A : System.{v, w} Y) (n : ℕ) :
    homologyMap f A n =
      (coefficientHomologyIso (pullbackIso f A) n).hom ≫
        pushforwardHomologyMap (map.{u, v, w} f) (system.{v, w, u} A) n := by
  simp only [homologyMap, chainMap, Functor.map_comp]
  rfl

/-- The canonical coefficient comparison does not change the isomorphism question. -/
theorem isIso_homologyMap_iff_lifted (f : C(X, Y)) (A : System.{v, w} Y) (n : ℕ) :
    IsIso (homologyMap f A n) ↔
      IsIso (pushforwardHomologyMap (map.{u, v, w} f) (system.{v, w, u} A) n) := by
  rw [homologyMap_eq, isIso_comp_left_iff]

section SameUniverse

variable {S T : Type u} [TopologicalSpace S] [TopologicalSpace T]

/-- In the existing universe, coefficient lifting has its canonical inverse. -/
def coefficientDownIso (A : System.{u, u} S) :
    system.{u, u, u} A ≅ pullback (down S) A :=
  NatIso.ofComponents (fun x => (fiberEquiv A x.as).toModuleIso) (by
    intro x y p
    obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective p
    ext a
    rfl)

/-- The actual coefficient-and-simplex comparison in each existing degree. -/
def moduleComparisonIso (A : System.{u, u} S) (n : SimplexCategory) :
    chainModule (system.{u, u, u} A) n ≅ chainModule A n where
  hom := Sigma.desc fun σ =>
    (coefficientDownIso A).hom.app (FundamentalGroupoid.mk (σ (Convexity.StdSimplex.single 0))) ≫
      chainInclusion A (simplexEquiv S n σ)
  inv := Sigma.desc fun σ =>
    (coefficientDownIso A).inv.app
        (FundamentalGroupoid.mk (ULift.up (σ (Convexity.StdSimplex.single 0)))) ≫
      chainInclusion (system.{u, u, u} A) ((simplexEquiv S n).symm σ)
  hom_inv_id := by
    apply Sigma.hom_ext
    intro σ
    simp only [chainInclusion, Category.assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc]
    change (coefficientDownIso A).hom.app
        (FundamentalGroupoid.mk (σ (Convexity.StdSimplex.single 0))) ≫
      ((coefficientDownIso A).inv.app (FundamentalGroupoid.mk (σ (Convexity.StdSimplex.single 0))) ≫
        chainInclusion (system.{u, u, u} A) σ) = _
    rw [← Category.assoc, Iso.hom_inv_id_app]
    simp [chainModule, chainInclusion]
  inv_hom_id := by
    apply Sigma.hom_ext
    intro σ
    simp only [chainInclusion, Category.assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc]
    change (coefficientDownIso A).inv.app
        (FundamentalGroupoid.mk (ULift.up (σ (Convexity.StdSimplex.single 0)))) ≫
      ((coefficientDownIso A).hom.app
        (FundamentalGroupoid.mk (ULift.up (σ (Convexity.StdSimplex.single 0)))) ≫
        chainInclusion A σ) = _
    rw [← Category.assoc, Iso.inv_hom_id_app]
    simp [chainModule, chainInclusion]

/-- The degreewise comparison is the specified coefficient and spatial map. -/
theorem moduleComparisonIso_hom (A : System.{u, u} S) (n : SimplexCategory) :
    (moduleComparisonIso A n).hom =
      coefficientModuleMap (coefficientDownIso A).hom n ≫
        pushforwardModuleMap (down S) A n := by
  apply Sigma.hom_ext
  intro σ
  simp [moduleComparisonIso, coefficientModuleMap, coefficientDownIso,
    pushforwardModuleMap, chainInclusion]
  rfl

/-- The same-universe comparison is a genuine simplicial isomorphism. -/
def simplicialComparisonIso (A : System.{u, u} S) :
    simplicialModule (system.{u, u, u} A) ≅ simplicialModule A :=
  NatIso.ofComponents (fun n => moduleComparisonIso A n.unop) (by
    intro n m α
    simpa only [moduleComparisonIso_hom, NatTrans.comp_app,
      coefficientSimplicialMap, pushforwardSimplicialMap] using
      (coefficientSimplicialMap (coefficientDownIso A).hom ≫
        pushforwardSimplicialMap (down S) A).naturality α)

/-- The same-universe comparison is an isomorphism of the actual chain complexes. -/
def chainComparisonIso (A : System.{u, u} S) :
    chainComplex.{u, u, u} A ≅ singularChainComplex A :=
  (AlgebraicTopology.alternatingFaceMapComplex _).mapIso (simplicialComparisonIso A)

/-- The induced comparison recovers the existing local-coefficient homology. -/
def homologyComparisonIso (A : System.{u, u} S) (n : ℕ) :
    homology.{u, u, u} A n ≅ LocalCoefficients.homology A n :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso (chainComparisonIso A)

/-- The comparison applies the projection homeomorphism and inverse coefficient lift
on each actual singular summand. -/
@[reassoc (attr := simp)]
theorem chainInclusion_chainComparisonIso (A : System.{u, u} S) {n : ℕ}
    (σ : SingularSimplex (ULift.{u} S) ⦋n⦌) :
    chainInclusion (system.{u, u, u} A) σ ≫ (chainComparisonIso A).hom.f n =
      (coefficientDownIso A).hom.app (FundamentalGroupoid.mk (σ (Convexity.StdSimplex.single 0))) ≫
        chainInclusion A (simplexEquiv S ⦋n⦌ σ) := by
  exact Sigma.ι_comp_desc _ _

/-- The original chain map is recovered in a commuting square of actual chain maps. -/
@[reassoc]
theorem chainComparisonIso_naturality (f : C(S, T)) (A : System.{u, u} T) :
    chainMap f A ≫ (chainComparisonIso A).hom =
      (chainComparisonIso (pullback f A)).hom ≫ pushforwardChainMap f A := by
  ext n : 1
  apply Sigma.hom_ext
  intro σ
  change chainInclusion (system.{u, u, u} (pullback f A)) σ ≫
      ((chainMap f A).f n ≫ (chainComparisonIso A).hom.f n) =
    chainInclusion (system.{u, u, u} (pullback f A)) σ ≫
      ((chainComparisonIso (pullback f A)).hom.f n ≫ (pushforwardChainMap f A).f n)
  rw [← Category.assoc, chainInclusion_chainMap, chainInclusion_chainComparisonIso,
    ← Category.assoc, chainInclusion_chainComparisonIso, Category.assoc]
  change _ = (coefficientDownIso (pullback f A)).hom.app
      (FundamentalGroupoid.mk (σ (Convexity.StdSimplex.single 0))) ≫
    (chainInclusion (pullback f A) (simplexEquiv S ⦋n⦌ σ) ≫
      pushforwardModuleMap f A ⦋n⦌)
  rw [chainInclusion_pushforwardModuleMap]
  rfl

/-- Its homology square recovers precisely the pre-existing induced homology map. -/
@[reassoc]
theorem homologyComparisonIso_naturality (f : C(S, T)) (A : System.{u, u} T) (n : ℕ) :
    homologyMap f A n ≫ (homologyComparisonIso A n).hom =
      (homologyComparisonIso (pullback f A) n).hom ≫ pushforwardHomologyMap f A n := by
  change (HomologicalComplex.homologyFunctor _ _ n).map (chainMap f A) ≫
      (HomologicalComplex.homologyFunctor _ _ n).map (chainComparisonIso A).hom =
    (HomologicalComplex.homologyFunctor _ _ n).map
        (chainComparisonIso (pullback f A)).hom ≫
      (HomologicalComplex.homologyFunctor _ _ n).map (pushforwardChainMap f A)
  rw [← Functor.map_comp, ← Functor.map_comp, chainComparisonIso_naturality]

/-- The lifted formulation and the original same-universe isomorphism assertion agree. -/
theorem isIso_homologyMap_iff (f : C(S, T)) (A : System.{u, u} T) (n : ℕ) :
    IsIso (homologyMap f A n) ↔ IsIso (pushforwardHomologyMap f A n) := by
  rw [← isIso_comp_right_iff _ (homologyComparisonIso A n).hom,
    homologyComparisonIso_naturality, isIso_comp_left_iff]

end SameUniverse

end FundamentalGroupoid.LocalCoefficients.UniverseLift
