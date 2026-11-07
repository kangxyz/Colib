/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.SimplexBoundary.ChartsHomotopy
public import Colib.Topology.LocalCoefficients.SimplexProductMaps
public import Colib.Topology.LocalCoefficients.TwoOpenDescent
public import Colib.Topology.LocalCoefficients.HomotopySquare
public import Colib.Topology.LocalCoefficients.Abelian

/-!
Adapted from `Quillen/Topology/LocalCoefficients/SimplexBoundaryProducts.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps.

# Abelian local-coefficient comparison on products with simplex boundaries

A continuous map inducing a quasi-isomorphism for every target system with
abelian monodromy has the same property after taking its product with the
identity of any finite simplex boundary. The proof uses explicit vertex charts,
their actual deformation equivalences, and two-open descent. It retains the
original spatial chain map and does not assume that arbitrary topological
products preserve pushouts or that the local system splits as a product.
-/

@[expose] public section

open Convexity
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open SSet TopCat StdSimplex
open CategoryTheory
open scoped ContinuousMap
universe u
namespace FundamentalGroupoid.LocalCoefficients

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

private theorem boundaryComparison_of_square
    {X' Y' : Type u} [TopologicalSpace X'] [TopologicalSpace Y']
    (eX : X ≃ₕ X') (eY : Y ≃ₕ Y') (f : C(X, Y)) (g : C(X', Y'))
    (h : g.comp eX.toFun = eY.toFun.comp f) (A : System.{u, u} Y')
    (hf : QuasiIso (pushforwardChainMap f (pullback eY.toFun A))) :
    QuasiIso (pushforwardChainMap g A) := by
  rw [quasiIso_iff]
  intro k
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact isIso_pushforwardHomologyMap_of_homotopySquare eX eY f g
    ((ContinuousMap.Homotopy.refl _).cast rfl h) A k (by
      change IsIso (HomologicalComplex.homologyMap _ k)
      infer_instance)

/-- Replacing the parameter by an explicitly homotopy-equivalent space preserves
the abelian coefficient comparison for the original product map. -/
theorem prodMap_id_quasiIso_of_parameter_homotopyEquiv
    {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q]
    (f : C(X, Y)) (e : P ≃ₕ Q)
    (hf : ∀ (A : System.{u, u} (Y × Q)), AbelianMonodromy A →
      QuasiIso (pushforwardChainMap (f.prodMap (ContinuousMap.id Q)) A))
    (A : System.{u, u} (Y × P)) (hA : AbelianMonodromy A) :
    QuasiIso (pushforwardChainMap (f.prodMap (ContinuousMap.id P)) A) := by
  let eX := (ContinuousMap.HomotopyEquiv.refl X).prodCongr e.symm
  let eY := (ContinuousMap.HomotopyEquiv.refl Y).prodCongr e.symm
  apply boundaryComparison_of_square eX eY
    (f.prodMap (ContinuousMap.id Q)) (f.prodMap (ContinuousMap.id P)) (by rfl) A
  exact hf _ (pullback_abelianMonodromy eY.toFun hA)

/-- Product with a point preserves the original abelian comparison. -/
theorem prodMap_id_punit_quasiIso (f : C(X, Y))
    (hf : ∀ (A : System.{u, u} Y), AbelianMonodromy A →
      QuasiIso (pushforwardChainMap f A))
    (A : System.{u, u} (Y × PUnit.{1})) (hA : AbelianMonodromy A) :
    QuasiIso (pushforwardChainMap (f.prodMap (ContinuousMap.id PUnit.{1})) A) := by
  let eX := (Homeomorph.prodPUnit X).symm.toHomotopyEquiv
  let eY := (Homeomorph.prodPUnit Y).symm.toHomotopyEquiv
  apply boundaryComparison_of_square eX eY f
    (f.prodMap (ContinuousMap.id PUnit.{1})) (by rfl) A
  exact hf _ (pullback_abelianMonodromy eY.toFun hA)

/-- The simplex product comparison uses the actual target vertex restriction. -/
theorem prodMap_id_simplex_quasiIso (f : C(X, Y))
    (hf : ∀ (A : System.{u, u} Y), AbelianMonodromy A →
      QuasiIso (pushforwardChainMap f A)) (n : ℕ)
    (A : System.{u, u} (Y × StdSimplex ℝ (Fin (n + 1)))) (hA : AbelianMonodromy A) :
    QuasiIso (pushforwardChainMap
      (f.prodMap (ContinuousMap.id (StdSimplex ℝ (Fin (n + 1))))) A) := by
  rw [quasiIso_iff]
  intro k
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply (simplexProductMap_homology_isIso_iff n n f _ rfl A k).mpr
  have := hf (pullback (simplexProductVertex Y n 0) A)
    (pullback_abelianMonodromy _ hA)
  change IsIso (HomologicalComplex.homologyMap _ k)
  infer_instance

/-- Product coordinates on the actual subspace cut out only in the parameter. -/
def parameterSubspaceHomeomorph (X : Type u) [TopologicalSpace X]
    {P : Type} [TopologicalSpace P] (W : Set P) :
    (X × W) ≃ₜ {z : X × P // z.2 ∈ W} where
  toFun z := ⟨(z.1, z.2.val), z.2.property⟩
  invFun z := (z.val.1, ⟨z.val.2, z.property⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Actual comparison on a parameter subspace, including its coefficient conversion. -/
theorem subspacePushforwardChainMap_prodMap_id_quasiIso
    {P : Type} [TopologicalSpace P] (f : C(X, Y)) (W : Set P)
    (hf : ∀ (A : System.{u, u} (Y × W)), AbelianMonodromy A →
      QuasiIso (pushforwardChainMap (f.prodMap (ContinuousMap.id W)) A))
    (A : System.{u, u} (Y × P)) (hA : AbelianMonodromy A) :
    QuasiIso (subspacePushforwardChainMap (f.prodMap (ContinuousMap.id P))
      {z : X × P | z.2 ∈ W} {z : Y × P | z.2 ∈ W} (fun _ h ↦ h) A) := by
  let U : Set (X × P) := {z | z.2 ∈ W}
  let V : Set (Y × P) := {z | z.2 ∈ W}
  let g := subspaceMap (f.prodMap (ContinuousMap.id P)) U V (fun _ h ↦ h)
  let B := pullback (subspaceInclusion V) A
  have hB : AbelianMonodromy B := pullback_abelianMonodromy _ hA
  have hg : QuasiIso (pushforwardChainMap g B) := by
    apply boundaryComparison_of_square (parameterSubspaceHomeomorph X W).toHomotopyEquiv
      (parameterSubspaceHomeomorph Y W).toHomotopyEquiv
      (f.prodMap (ContinuousMap.id W)) g (by rfl) B
    exact hf _ (pullback_abelianMonodromy _ hB)
  change QuasiIso ((coefficientChainIso
    (subspaceMapPullbackIso (f.prodMap (ContinuousMap.id P)) U V (fun _ h ↦ h) A)).hom ≫
      pushforwardChainMap g B)
  infer_instance

/-- Comparisons on two open parameter charts and their intersection imply the
comparison for the original product map. -/
theorem prodMap_id_quasiIso_of_two_open
    {P : Type} [TopologicalSpace P] (f : C(X, Y)) (U V : Set P)
    (openU : IsOpen U) (openV : IsOpen V) (cover : U ∪ V = Set.univ)
    (hU : ∀ (A : System.{u, u} (Y × U)), AbelianMonodromy A →
      QuasiIso (pushforwardChainMap (f.prodMap (ContinuousMap.id U)) A))
    (hV : ∀ (A : System.{u, u} (Y × V)), AbelianMonodromy A →
      QuasiIso (pushforwardChainMap (f.prodMap (ContinuousMap.id V)) A))
    (hUV : ∀ (A : System.{u, u} (Y × ↥(U ∩ V))), AbelianMonodromy A →
      QuasiIso (pushforwardChainMap (f.prodMap (ContinuousMap.id ↥(U ∩ V))) A))
    (A : System.{u, u} (Y × P)) (hA : AbelianMonodromy A) :
    QuasiIso (pushforwardChainMap (f.prodMap (ContinuousMap.id P)) A) := by
  have cov (Z : Type u) : {z : Z × P | z.2 ∈ U} ∪ {z | z.2 ∈ V} = Set.univ := by
    ext z
    have hz : z.2 ∈ U ∪ V := by rw [cover]; trivial
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact hz
  apply pushforwardChainMap_quasiIso_of_two_open_subspaces
    (f.prodMap (ContinuousMap.id P))
    {z : X × P | z.2 ∈ U} {z : X × P | z.2 ∈ V}
    {z : Y × P | z.2 ∈ U} {z : Y × P | z.2 ∈ V} A
    (fun _ h ↦ h) (fun _ h ↦ h)
    (openU.preimage continuous_snd) (openV.preimage continuous_snd) (cov X)
    (openU.preimage continuous_snd) (openV.preimage continuous_snd) (cov Y)
  · exact subspacePushforwardChainMap_prodMap_id_quasiIso f U hU A hA
  · exact subspacePushforwardChainMap_prodMap_id_quasiIso f V hV A hA
  · exact subspacePushforwardChainMap_prodMap_id_quasiIso f (U ∩ V) hUV A hA

/-- The empty zero-dimensional boundary gives an actual chain quasi-isomorphism. -/
theorem prodMap_id_simplexBoundary_zero_quasiIso (f : C(X, Y))
    (A : System.{u, u} (Y × StdSimplex.boundary 0)) :
    QuasiIso (pushforwardChainMap
      (f.prodMap (ContinuousMap.id (StdSimplex.boundary 0))) A) := by
  let : IsEmpty (StdSimplex.boundary 0) := isEmpty_boundary_zero
  let e : (X × StdSimplex.boundary 0) ≃ₜ (Y × StdSimplex.boundary 0) :=
    Homeomorph.empty
  have he : e.toHomotopyEquiv.toFun = f.prodMap
    (ContinuousMap.id (StdSimplex.boundary 0)) := by
    apply ContinuousMap.ext
    intro z
    exact isEmptyElim z.2
  rw [← he, quasiIso_iff]
  intro k
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact isIso_pushforwardHomologyMap_of_homotopyEquiv e.toHomotopyEquiv A k

/-- Products with every finite simplex boundary preserve comparison with every
possibly nonconstant abelian target local system, on the original spatial map. -/
theorem prodMap_id_simplexBoundary_quasiIso (f : C(X, Y))
    (hf : ∀ (A : System.{u, u} Y), AbelianMonodromy A →
      QuasiIso (pushforwardChainMap f A)) (n : ℕ)
    (A : System.{u, u} (Y × StdSimplex.boundary n)) (hA : AbelianMonodromy A) :
    QuasiIso (pushforwardChainMap
      (f.prodMap (ContinuousMap.id (StdSimplex.boundary n))) A) := by
  induction n with
  | zero => exact prodMap_id_simplexBoundary_zero_quasiIso f A
  | succ n ih =>
    apply prodMap_id_quasiIso_of_two_open f (simplexBoundaryLower n) (simplexBoundaryUpper n)
      (isOpen_simplexBoundaryLower n) (isOpen_simplexBoundaryUpper n)
      (simplexBoundaryLower_union_upper n) _ _ _ A hA
    · intro B hB
      exact prodMap_id_quasiIso_of_parameter_homotopyEquiv f (simplexBoundaryLowerEquiv n)
        (prodMap_id_simplex_quasiIso f hf n) B hB
    · intro B hB
      exact prodMap_id_quasiIso_of_parameter_homotopyEquiv f (simplexBoundaryUpperEquiv n)
        (prodMap_id_punit_quasiIso f hf) B hB
    · intro B hB
      exact prodMap_id_quasiIso_of_parameter_homotopyEquiv f (simplexBoundaryOverlapEquiv n)
        ih B hB

/-- In dimension one the overlap is empty, and the original endpoint product map
is still the quasi-isomorphism furnished by the all-dimensional theorem. -/
theorem prodMap_id_simplexBoundary_one_quasiIso (f : C(X, Y))
    (hf : ∀ (A : System.{u, u} Y), AbelianMonodromy A →
      QuasiIso (pushforwardChainMap f A))
    (A : System.{u, u} (Y × StdSimplex.boundary 1)) (hA : AbelianMonodromy A) :
    QuasiIso (pushforwardChainMap
      (f.prodMap (ContinuousMap.id (StdSimplex.boundary 1))) A) :=
  prodMap_id_simplexBoundary_quasiIso f hf 1 A hA

end FundamentalGroupoid.LocalCoefficients
