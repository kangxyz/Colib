/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.LocalCoefficients.MarkedSphericalTwoCycle
public import Colib.Topology.LocalCoefficients.Prism
public import Colib.Topology.LocalCoefficients.HomotopyInvariance
public import Colib.Topology.Homotopy.HomotopyGroup.SphericalHomotopyAddition
public import Colib.Topology.Homotopy.HomotopyGroup.SphericalSimplexMap
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransportFundamentalGroup
public import Colib.Topology.Homotopy.HomotopyGroup.SphericalHorn
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Tactic.Abel

/-!
# The original marked second Hurewicz homomorphism

A based spherical triangle is sent to its literal sphere-minus-constant
cycle in the original unnormalized integral singular complex. The explicit
stick-breaking quotient identifies this representative with the original
cubical Pi-two class. A three-prism boundary proves relative homotopy
invariance. A concrete barycentric retraction fills the three-face horn;
the accepted signed tetrahedral homotopy formula and the original chain
differential prove additivity with the same increasing-vertex orientation.

The resulting homomorphism is natural for the original based Pi-two maps
and original integral homology maps, and retains every original basepoint
path. No simple-connectedness or homology comparison law is assumed.
The separate injectivity leaf applies the finite-cap descent theorem when
the target is simply connected.
-/
/-! Implementation source: `Quillen/Topology/LocalCoefficients/SecondHurewicz.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Native simplex coordinates,
original maps, endpoint paths, coefficient universe and chain signs are retained.
The spherical representatives use the explicit ordered stick-breaking quotient.
-/
@[expose] public section

open Convexity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Limits Topology
open scoped Simplicial Topology unitInterval

namespace FundamentalGroupoid.LocalCoefficients.SecondHurewicz
variable {Y : Type u} [TopologicalSpace Y] {y : Y}

/-- The original unnormalized singular complex with its lifted integral coefficient object. -/
abbrev Chains (Y : Type u) [TopologicalSpace Y] :=
  singularChainComplex (constant Y integralCoefficients.{u})

/-- The original integral generator with coefficient exactly the lifted integer one. -/
def simplexChain {n : ℕ} (τ : SingularSimplex Y ⦋n⦌) : (Chains Y).X n :=
  chainInclusion (constant Y integralCoefficients.{u}) τ (ULift.up 1)

/-- The original differential of an integral tetrahedron, with all four face signs. -/
theorem tetrahedron_boundary (τ : SingularSimplex Y ⦋3⦌) :
    (Chains Y).d 3 2 (simplexChain τ) =
      simplexChain (restrictSimplex τ (SimplexCategory.δ 0)) -
      simplexChain (restrictSimplex τ (SimplexCategory.δ 1)) +
      simplexChain (restrictSimplex τ (SimplexCategory.δ 2)) -
      simplexChain (restrictSimplex τ (SimplexCategory.δ 3)) := by
  let ev : (integralCoefficients.{u} ⟶ (Chains Y).X 2) →+ (Chains Y).X 2 := {
    toFun f := f (ULift.up 1)
    map_zero' := rfl
    map_add' _ _ := rfl }
  have h := congrArg ev (chainInclusion_d (constant Y integralCoefficients.{u}) τ)
  change _ = ev _ at h
  simp only [Nat.reduceAdd, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ModuleCat.hom_comp,
    LinearMap.coe_comp, Function.comp_apply, Int.reduceNeg, integralRestrictionTransport,
    Fin.sum_univ_succ, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, pow_zero, one_smul,
    Fin.val_succ, zero_add, pow_one, Fin.succ_zero_eq_one, neg_smul, add_assoc, even_two,
    Even.neg_pow, one_pow, Fin.succ_one_eq_two, Finset.univ_unique, Fin.default_eq_zero,
    Fin.val_eq_zero, Int.reducePow, Finset.sum_neg_distrib, Finset.sum_singleton, Fin.reduceSucc,
    ModuleCat.hom_add, ModuleCat.hom_id, LinearMap.comp_id, ModuleCat.hom_neg,
    LinearMap.add_apply, LinearMap.neg_apply, ev] at h
  change ((Chains Y).d 3 2).hom
      ((chainInclusion (constant Y integralCoefficients.{u}) τ).hom (ULift.up 1)) = _
  change _ = simplexChain (restrictSimplex τ (SimplexCategory.δ 0)) +
    (-simplexChain (restrictSimplex τ (SimplexCategory.δ 1)) +
      (simplexChain (restrictSimplex τ (SimplexCategory.δ 2)) +
        -simplexChain (restrictSimplex τ (SimplexCategory.δ 3)))) at h
  exact h.trans (by abel)

/-- The original marked homology class of a spherical triangle. -/
def sphericalClass (a : SphericalSimplex Y y 2) :
    homology (constant Y integralCoefficients) 2 :=
  (Chains Y).homologyπ 2 (sphericalTwoCycle a)

/-- An actual differential equality gives equality in the original homology object. -/
theorem homology_eq_of_boundary (a b : (Chains Y).cycles 2) (c : (Chains Y).X 3)
    (hc : (Chains Y).d 3 2 c = (Chains Y).iCycles 2 a - (Chains Y).iCycles 2 b) :
    (Chains Y).homologyπ 2 a = (Chains Y).homologyπ 2 b := by
  have hz : a - b = (Chains Y).toCycles 3 2 c := by
    apply (ModuleCat.mono_iff_injective ((Chains Y).iCycles 2)).mp inferInstance
    rw [map_sub]
    exact hc.symm.trans
      (ConcreteCategory.congr_hom ((Chains Y).toCycles_i 3 2) c).symm
  apply sub_eq_zero.mp
  rw [← map_sub, hz]
  exact ConcreteCategory.congr_hom ((Chains Y).toCycles_comp_homologyπ 3 2) c

/-- The actual constant spherical triangle gives zero under the marked chain convention. -/
theorem sphericalClass_const :
    sphericalClass (SphericalSimplex.const : SphericalSimplex Y y 2) = 0 := by
  have hz : sphericalTwoCycle (SphericalSimplex.const : SphericalSimplex Y y 2) = 0 := by
    apply (ModuleCat.mono_iff_injective ((Chains Y).iCycles 2)).mp inferInstance
    rw [map_zero, iCycles_sphericalTwoCycle, sphericalTwoChain]
    exact sub_self _
  rw [sphericalClass, hz, map_zero]

end FundamentalGroupoid.LocalCoefficients.SecondHurewicz

namespace FundamentalGroupoid.LocalCoefficients.SecondHurewicz
variable {Y : Type u} [TopologicalSpace Y] {y : Y}
  {a b : SphericalSimplex Y y 2}
  (H : a.val.HomotopyRel b.val (StdSimplex.boundary 2))

/-- The original triangle with only its universe lifted. -/
def triangleUp : SingularSimplex (ULift.{u} (StdSimplex ℝ (Fin 3))) ⦋2⦌ :=
  ⟨ULift.up, continuous_uliftUp⟩

/-- The whole relative homotopy with its simplex source lifted
to the coefficient universe. -/
def liftedHomotopy :
    (a.val.comp ⟨ULift.down, continuous_uliftDown⟩).Homotopy
      (b.val.comp ⟨ULift.down, continuous_uliftDown⟩) :=
  H.toHomotopy.compContinuousMap ⟨ULift.down, continuous_uliftDown⟩

/-- The three original standard prism tetrahedra for the full relative homotopy. -/
def prismTriangle (i : Fin 3) : SingularSimplex Y ⦋3⦌ :=
  prismSimplex (liftedHomotopy H) i triangleUp

private theorem sidePrism_const (i : Fin 2) (j : Fin 3) :
    prismSimplex (liftedHomotopy H) i
      (restrictSimplex triangleUp (SimplexCategory.δ j)) = ContinuousMap.const _ y := by
  ext z
  rw [prismSimplex_apply]
  change H (_, StdSimplex.map (SimplexCategory.δ j) (StdSimplex.map (SimplexCategory.σ i) z)) = y
  have hz : StdSimplex.map (SimplexCategory.δ j)
      (StdSimplex.map (SimplexCategory.σ i) z) ∈ StdSimplex.boundary 2 :=
    (StdSimplex.simplexBoundaryFace 1 j (StdSimplex.map (SimplexCategory.σ i) z)).property
  exact (H.eq_fst _ hz).trans (a.boundary _ hz)

private theorem prismTriangle_first :
    restrictSimplex (prismTriangle H 0) (SimplexCategory.δ 0) = b.val :=
  prismSimplex_face_zero (liftedHomotopy H) triangleUp

private theorem prismTriangle_last :
    restrictSimplex (prismTriangle H 2) (SimplexCategory.δ 3) = a.val :=
  prismSimplex_face_last (liftedHomotopy H) triangleUp

private theorem prismTriangle_middle0 :
    restrictSimplex (prismTriangle H 0) (SimplexCategory.δ 1) =
      restrictSimplex (prismTriangle H 1) (SimplexCategory.δ 1) :=
  (prismSimplex_middle_face (liftedHomotopy H) (0 : Fin 2) triangleUp).symm

private theorem prismTriangle_middle1 :
    restrictSimplex (prismTriangle H 1) (SimplexCategory.δ 2) =
      restrictSimplex (prismTriangle H 2) (SimplexCategory.δ 2) :=
  (prismSimplex_middle_face (liftedHomotopy H) (1 : Fin 2) triangleUp).symm

private theorem prismTriangle_side02 :
    restrictSimplex (prismTriangle H 0) (SimplexCategory.δ 2) = ContinuousMap.const _ y :=
  (prismSimplex_face_of_lt (liftedHomotopy H) (1 : Fin 3) (0 : Fin 2) (by decide)
    triangleUp).trans (sidePrism_const H 0 1)

private theorem prismTriangle_side03 :
    restrictSimplex (prismTriangle H 0) (SimplexCategory.δ 3) = ContinuousMap.const _ y :=
  (prismSimplex_face_of_lt (liftedHomotopy H) (2 : Fin 3) (0 : Fin 2) (by decide)
    triangleUp).trans (sidePrism_const H 0 2)

private theorem prismTriangle_side10 :
    restrictSimplex (prismTriangle H 1) (SimplexCategory.δ 0) = ContinuousMap.const _ y :=
  (prismSimplex_face_of_le (liftedHomotopy H) (0 : Fin 3) (0 : Fin 2) (by decide)
    triangleUp).trans (sidePrism_const H 0 0)

private theorem prismTriangle_side13 :
    restrictSimplex (prismTriangle H 1) (SimplexCategory.δ 3) = ContinuousMap.const _ y :=
  (prismSimplex_face_of_lt (liftedHomotopy H) (2 : Fin 3) (1 : Fin 2) (by decide)
    triangleUp).trans (sidePrism_const H 1 2)

private theorem prismTriangle_side20 :
    restrictSimplex (prismTriangle H 2) (SimplexCategory.δ 0) = ContinuousMap.const _ y :=
  (prismSimplex_face_of_le (liftedHomotopy H) (0 : Fin 3) (1 : Fin 2) (by decide)
    triangleUp).trans (sidePrism_const H 1 0)

private theorem prismTriangle_side21 :
    restrictSimplex (prismTriangle H 2) (SimplexCategory.δ 1) = ContinuousMap.const _ y :=
  (prismSimplex_face_of_le (liftedHomotopy H) (1 : Fin 3) (1 : Fin 2) (by decide)
    triangleUp).trans (sidePrism_const H 1 1)

/-- The literal alternating three-prism chain. -/
def prismChain : (Chains Y).X 3 :=
  simplexChain (prismTriangle H 0) - simplexChain (prismTriangle H 1) +
    simplexChain (prismTriangle H 2)

/-- Its original boundary is the terminal spherical generator minus the initial one. -/
theorem prismChain_boundary :
    (Chains Y).d 3 2 (prismChain H) = simplexChain b.val - simplexChain a.val := by
  rw [prismChain, map_add, map_sub, tetrahedron_boundary, tetrahedron_boundary,
    tetrahedron_boundary, prismTriangle_first, prismTriangle_last,
    prismTriangle_middle0, prismTriangle_middle1,
    prismTriangle_side02, prismTriangle_side03, prismTriangle_side10,
    prismTriangle_side13, prismTriangle_side20, prismTriangle_side21]
  abel

include H in
/-- Relative homotopy preserves the original marked absolute homology class. -/
theorem sphericalClass_homotopy : sphericalClass a = sphericalClass b := by
  symm
  apply homology_eq_of_boundary (sphericalTwoCycle b) (sphericalTwoCycle a) (prismChain H)
  rw [prismChain_boundary, iCycles_sphericalTwoCycle, iCycles_sphericalTwoCycle]
  change simplexChain b.val - simplexChain a.val =
    (simplexChain b.val - simplexChain (ContinuousMap.const _ y)) -
      (simplexChain a.val - simplexChain (ContinuousMap.const _ y))
  abel

end FundamentalGroupoid.LocalCoefficients.SecondHurewicz



namespace FundamentalGroupoid.LocalCoefficients.SecondHurewicz
variable {Y : Type u} [TopologicalSpace Y] {y : Y}

/-- The ordered addition horn consists of the first sphere, second sphere,
and constant sphere. -/
def additionFaces (a b : SphericalSimplex Y y 2) :
    Fin 3 → SphericalSimplex Y y 2 :=
  ![a, b, SphericalSimplex.const]

/-- The actual missing face in the displayed three-spherical-face tetrahedron. -/
def sumSphere (a b : SphericalSimplex Y y 2) : SphericalSimplex Y y 2 :=
  sphericalFace (SphericalHorn.fill (additionFaces a b))
    (SphericalHorn.fill_skeleton (additionFaces a b)) 1

private theorem addition_face0 (a b : SphericalSimplex Y y 2) :
    sphericalFace (SphericalHorn.fill (additionFaces a b))
      (SphericalHorn.fill_skeleton (additionFaces a b)) 0 = a :=
  SphericalHorn.sphericalFace_fill (additionFaces a b) 0

private theorem addition_face2 (a b : SphericalSimplex Y y 2) :
    sphericalFace (SphericalHorn.fill (additionFaces a b))
      (SphericalHorn.fill_skeleton (additionFaces a b)) 2 = b :=
  SphericalHorn.sphericalFace_fill (additionFaces a b) 1

private theorem addition_face3 (a b : SphericalSimplex Y y 2) :
    sphericalFace (SphericalHorn.fill (additionFaces a b))
      (SphericalHorn.fill_skeleton (additionFaces a b)) 3 = SphericalSimplex.const :=
  SphericalHorn.sphericalFace_fill (additionFaces a b) 2

/-- The missing face represents the original product in cubical Pi two, with the fixed sign. -/
theorem sumSphere_class (a b : SphericalSimplex Y y 2) :
    (sumSphere a b).homotopyClassStick = a.homotopyClassStick * b.homotopyClassStick := by
  have h := spherical_tetrahedral_homotopy_addition
    (SphericalHorn.fill (additionFaces a b))
    (SphericalHorn.fill_skeleton (additionFaces a b))
  rw [addition_face0, addition_face2, addition_face3, SphericalSimplex.homotopyClassStick_const]
    at h
  change Additive.ofMul a.homotopyClassStick - Additive.ofMul (sumSphere a b).homotopyClassStick +
    Additive.ofMul b.homotopyClassStick - 0 = 0 at h
  rw [sub_zero] at h
  have he : Additive.ofMul a.homotopyClassStick + Additive.ofMul b.homotopyClassStick =
      Additive.ofMul (sumSphere a b).homotopyClassStick := by
    apply sub_eq_zero.mp
    calc
      _ = Additive.ofMul a.homotopyClassStick -
          Additive.ofMul (sumSphere a b).homotopyClassStick +
            Additive.ofMul b.homotopyClassStick := by abel
      _ = 0 := h
  exact congrArg Additive.toMul he.symm

/-- The same actual tetrahedron proves addition of the original marked homology classes. -/
theorem sphericalClass_sumSphere (a b : SphericalSimplex Y y 2) :
    sphericalClass (sumSphere a b) = sphericalClass a + sphericalClass b := by
  let τ := SphericalHorn.fill (additionFaces a b)
  have h0 : restrictSimplex τ (SimplexCategory.δ 0) = a.val :=
    congrArg Subtype.val (addition_face0 a b)
  have h2 : restrictSimplex τ (SimplexCategory.δ 2) = b.val :=
    congrArg Subtype.val (addition_face2 a b)
  have h3 : restrictSimplex τ (SimplexCategory.δ 3) = ContinuousMap.const _ y :=
    congrArg Subtype.val (addition_face3 a b)
  have h := homology_eq_of_boundary (sphericalTwoCycle a + sphericalTwoCycle b)
    (sphericalTwoCycle (sumSphere a b)) (simplexChain τ) (by
      rw [tetrahedron_boundary, h0, h2, h3, map_add,
        iCycles_sphericalTwoCycle, iCycles_sphericalTwoCycle, iCycles_sphericalTwoCycle]
      change simplexChain a.val - simplexChain (sumSphere a b).val + simplexChain b.val -
        simplexChain (ContinuousMap.const _ y) =
          (simplexChain a.val - simplexChain (ContinuousMap.const _ y)) +
          (simplexChain b.val - simplexChain (ContinuousMap.const _ y)) -
          (simplexChain (sumSphere a b).val - simplexChain (ContinuousMap.const _ y))
      abel)
  rw [map_add] at h
  exact h.symm

/-- The original marked class descends through the actual based-cube homotopy quotient. -/
def toHomology (y : Y) :
    HomotopyGroup.Pi 2 Y y → homology (constant Y integralCoefficients) 2 :=
  Quotient.lift (fun p => sphericalClass (SphericalSimplex.ofGenLoopStick p)) (by
    intro p q hpq
    have he : (SphericalSimplex.ofGenLoopStick p).homotopyClassStick =
        (SphericalSimplex.ofGenLoopStick q).homotopyClassStick := by
      simp only [SphericalSimplex.homotopyClassStick,
        SphericalSimplex.toGenLoopStick_ofGenLoopStick]
      exact Quotient.sound hpq
    obtain ⟨H⟩ := (SphericalSimplex.homotopyClassStick_eq_iff _ _).mp he
    exact sphericalClass_homotopy H)

/-- Every spherical representative has precisely the specified original cycle class. -/
theorem toHomology_spherical (a : SphericalSimplex Y y 2) :
    toHomology y a.homotopyClassStick = sphericalClass a := by
  change sphericalClass (SphericalSimplex.ofGenLoopStick a.toGenLoopStick) = _
  rw [SphericalSimplex.ofGenLoopStick_toGenLoopStick]

/-- The actual constant cube maps to the zero class. -/
theorem toHomology_one : toHomology y 1 = 0 :=
  (toHomology_spherical (SphericalSimplex.const : SphericalSimplex Y y 2)).trans
    sphericalClass_const

/-- Original cube concatenation is sent to addition of the marked original homology classes. -/
theorem toHomology_mul (a b : HomotopyGroup.Pi 2 Y y) :
    toHomology y (a * b) = toHomology y a + toHomology y b := by
  obtain ⟨a, rfl⟩ := SphericalSimplex.homotopyClassStick_surjective a
  obtain ⟨b, rfl⟩ := SphericalSimplex.homotopyClassStick_surjective b
  rw [← sumSphere_class, toHomology_spherical, toHomology_spherical, toHomology_spherical]
  exact sphericalClass_sumSphere a b

/-- The marked second Hurewicz homomorphism into original integral H-two. -/
def hom (y : Y) : HomotopyGroup.Pi 2 Y y →*
    Multiplicative (homology (constant Y integralCoefficients.{u}) 2) where
  toFun a := Multiplicative.ofAdd (toHomology y a)
  map_one' := congrArg Multiplicative.ofAdd toHomology_one
  map_mul' a b := congrArg Multiplicative.ofAdd (toHomology_mul a b)

/-- The homomorphism retains the original sphere-minus-constant cycle and stick orientation. -/
theorem hom_spherical (a : SphericalSimplex Y y 2) :
    hom y a.homotopyClassStick = Multiplicative.ofAdd
      ((Chains Y).homologyπ 2 (sphericalTwoCycle a)) :=
  congrArg Multiplicative.ofAdd (toHomology_spherical a)

end FundamentalGroupoid.LocalCoefficients.SecondHurewicz

namespace FundamentalGroupoid.LocalCoefficients.SecondHurewicz
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y} (f : C(X, Y)) (h : f x = y)

/-- The explicit stick quotient preserves the original based postcomposition map. -/
theorem stickClass_map (a : SphericalSimplex X x 2) :
    (SphericalSimplex.map f h a).homotopyClassStick =
      HomotopyGroup.piMap 1 f h a.homotopyClassStick := rfl

private theorem pushforward_simplexChain {n : ℕ} (a : SingularSimplex X ⦋n⦌) :
    (pushforwardChainMap f (constant Y integralCoefficients.{u})).f n (simplexChain a) =
      simplexChain (f.comp a) :=
  ConcreteCategory.congr_hom
    (chainInclusion_pushforwardModuleMap f (constant Y integralCoefficients.{u}) a)
      (ULift.up 1)

/-- The original chain map sends the marked spherical difference to its actual based image. -/
theorem sphericalTwoChain_map (a : SphericalSimplex X x 2) :
    (pushforwardChainMap f (constant Y integralCoefficients.{u})).f 2 (sphericalTwoChain a) =
      sphericalTwoChain (SphericalSimplex.map f h a) := by
  change (pushforwardChainMap f (constant Y integralCoefficients.{u})).f 2
      (simplexChain a.val - simplexChain (ContinuousMap.const _ x)) = _
  rw [map_sub, pushforward_simplexChain, pushforward_simplexChain]
  have hc : f.comp (ContinuousMap.const (StdSimplex ℝ (Fin 3)) x) =
      ContinuousMap.const _ y := by ext t; exact h
  rw [hc]
  rfl

/-- The original categorical cycle map retains that exact marked spherical cycle. -/
theorem sphericalTwoCycle_map (a : SphericalSimplex X x 2) :
    HomologicalComplex.cyclesMap
      (pushforwardChainMap f (constant Y integralCoefficients.{u})) 2 (sphericalTwoCycle a) =
      sphericalTwoCycle (SphericalSimplex.map f h a) := by
  apply (ModuleCat.mono_iff_injective ((Chains Y).iCycles 2)).mp inferInstance
  have hn := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i
      (pushforwardChainMap f (constant Y integralCoefficients.{u})) 2) (sphericalTwoCycle a)
  change (Chains Y).iCycles 2 (HomologicalComplex.cyclesMap
        (pushforwardChainMap f (constant Y integralCoefficients.{u})) 2
          (sphericalTwoCycle a)) =
    (pushforwardChainMap f (constant Y integralCoefficients.{u})).f 2
      ((Chains X).iCycles 2 (sphericalTwoCycle a)) at hn
  rw [hn, iCycles_sphericalTwoCycle, iCycles_sphericalTwoCycle]
  exact sphericalTwoChain_map f h a

/-- Actual homology-map naturality on the original marked spherical representatives. -/
theorem sphericalClass_map (a : SphericalSimplex X x 2) :
    pushforwardHomologyMap f (constant Y integralCoefficients.{u}) 2 (sphericalClass a) =
      sphericalClass (SphericalSimplex.map f h a) := by
  have hn := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality
      (pushforwardChainMap f (constant Y integralCoefficients.{u})) 2) (sphericalTwoCycle a)
  change pushforwardHomologyMap f (constant Y integralCoefficients.{u}) 2
      (sphericalClass a) = (Chains Y).homologyπ 2
      (HomologicalComplex.cyclesMap
        (pushforwardChainMap f (constant Y integralCoefficients.{u})) 2
          (sphericalTwoCycle a)) at hn
  exact hn.trans (congrArg ((Chains Y).homologyπ 2) (sphericalTwoCycle_map f h a))

/-- The marked Hurewicz map is natural for the original based Pi-two and integral H-two maps. -/
theorem toHomology_naturality (a : HomotopyGroup.Pi 2 X x) :
    toHomology y (HomotopyGroup.piMap 1 f h a) =
      pushforwardHomologyMap f (constant Y integralCoefficients.{u}) 2 (toHomology x a) := by
  obtain ⟨a, rfl⟩ := SphericalSimplex.homotopyClassStick_surjective a
  rw [← stickClass_map, toHomology_spherical, toHomology_spherical]
  exact (sphericalClass_map f h a).symm

/-- The same naturality statement in the original multiplicative target notation. -/
theorem hom_naturality (a : HomotopyGroup.Pi 2 X x) :
    hom y (HomotopyGroup.piMap 1 f h a) = Multiplicative.ofAdd
      (pushforwardHomologyMap f (constant Y integralCoefficients.{u}) 2
        (Multiplicative.toAdd (hom x a))) :=
  congrArg Multiplicative.ofAdd (toHomology_naturality f h a)

private theorem constantHomologyMap_homotopy {f g : C(X, Y)} (H : f.Homotopy g) (n : ℕ) :
    pushforwardHomologyMap f (constant Y integralCoefficients.{u}) n =
      pushforwardHomologyMap g (constant Y integralCoefficients.{u}) n := by
  have hη : (homotopyPullbackIso H (constant Y integralCoefficients.{u})).hom =
      𝟙 (constant X integralCoefficients.{u}) := by
    ext z
    rfl
  have ht := pushforwardHomologyMap_homotopy H (constant Y integralCoefficients.{u}) n
  change pushforwardHomologyMap f (constant Y integralCoefficients.{u}) n =
    coefficientHomologyMap
      (homotopyPullbackIso H (constant Y integralCoefficients.{u})).hom n ≫
      pushforwardHomologyMap g (constant Y integralCoefficients.{u}) n at ht
  rw [hη] at ht
  erw [coefficientHomologyMap_id] at ht
  exact ht.trans (Category.id_comp _)

/-- The original basepoint transport does not change the marked integral H-two class. -/
theorem toHomology_pathTransport {z : Y} (p : Path y z) (a : HomotopyGroup.Pi 2 Y y) :
    toHomology z (pathTransport p 2 a) = toHomology y a := by
  obtain ⟨b, rfl⟩ := (pathStartEquiv p 2).surjective a
  rw [pathStartEquiv_apply, pathTransport_homotopyGroupMap_start]
  change toHomology z (HomotopyGroup.piMap 1 (freePathEvaluation Y 1) p.target b) =
    toHomology y (HomotopyGroup.piMap 1 (freePathEvaluation Y 0) p.source b)
  rw [toHomology_naturality, toHomology_naturality]
  exact congrArg (fun k => k (toHomology p.toContinuousMap b))
    (constantHomologyMap_homotopy freePathEvaluationHomotopy 2).symm

/-- Path correction is retained exactly by the multiplicative second Hurewicz map. -/
theorem hom_pathTransport {z : Y} (p : Path y z) (a : HomotopyGroup.Pi 2 Y y) :
    hom z (pathTransportMulEquiv p 1 a) = hom y a :=
  congrArg Multiplicative.ofAdd (toHomology_pathTransport p a)

end FundamentalGroupoid.LocalCoefficients.SecondHurewicz

namespace FundamentalGroupoid.LocalCoefficients.SecondHurewicz
variable {Y : Type u} [TopologicalSpace Y] {y : Y}

/-- Every original based two-cube maps to the literal cycle of its stick-descended sphere. -/
theorem hom_genLoop (p : GenLoop (Fin 2) Y y) :
    hom y (Quotient.mk' p) = Multiplicative.ofAdd
      ((Chains Y).homologyπ 2 (sphericalTwoCycle (SphericalSimplex.ofGenLoopStick p))) := by
  have h := hom_spherical (SphericalSimplex.ofGenLoopStick p)
  simpa only [SphericalSimplex.homotopyClassStick,
    SphericalSimplex.toGenLoopStick_ofGenLoopStick] using h

end FundamentalGroupoid.LocalCoefficients.SecondHurewicz
