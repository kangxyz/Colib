/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.FiberwiseMappingPath.Basic
public import Colib.Topology.HELP.ContractibleTestFullOverBase
public import Colib.Topology.HomotopyLifting.CubeDuration
public import Colib.Topology.CubicalSubdivision.BoundaryLifting

/-! # Literal boundary lifting for the vertical endpoint

Full over-base HELP retains the entire originally stored boundary path.
Packing the resulting vertical homotopy therefore gives a strict lift,
including equality of the complete boundary path coordinate.


Implementation provenance:
`Quillen/Topology/FiberwiseMappingPath/BoundaryLifting.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.FiberwiseMappingPath
variable {E F B : Type u} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]

/-- Full prescribed vertical HELP on one actual pair gives strict endpoint RLP. -/
theorem endpoint_hasLiftingProperty_of_pairHELP
    (q : C(F, B)) (f : C(E, F)) {A D : TopCat.{u}} (i : A ⟶ D)
    (hf : ∀ (a : C(A, E)) (b : C(D, F)) (H : (f.comp a).Homotopy (b.comp i.hom)),
      (∀ t x, q (H (t, x)) = q (b (i x))) →
      ∃ c : C(D, E), c.comp i.hom = a ∧ ∃ K : (f.comp c).Homotopy b,
        HomotopyOver (q.comp b) q K ∧ ∀ t x, K (t, i x) = H (t, x)) :
    HasLiftingProperty i (TopCat.ofHom (endpoint q f)) where
  sq_hasLift {a b} sq := by
    let H : (f.comp ((source q f).comp a.hom)).Homotopy (b.hom.comp i.hom) := {
      toFun z := (a z.2).val.2 z.1
      continuous_toFun := by fun_prop
      map_zero_left x := (a x).property.1
      map_one_left x := ConcreteCategory.congr_hom sq.w x }
    have hH (t : unitInterval) (x : A) : q (H (t,x)) = q (b (i x)) :=
      ((a x).property.2 t).trans (((a x).property.2 1).symm.trans
        (congrArg q (ConcreteCategory.congr_hom sq.w x)))
    obtain ⟨c,hc,K,hK,hA⟩ := hf ((source q f).comp a.hom) b.hom H hH
    let l : C(D,Space q f) := {
      toFun x := ⟨(c x,⟨fun t ↦ K (t,x),by fun_prop⟩),K.map_zero_left x,
        fun t ↦ (hK t x).trans ((hK 0 x).symm.trans (congrArg q (K.map_zero_left x)))⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply Continuous.prodMk c.continuous
        apply ContinuousMap.continuous_of_continuous_uncurry
        exact K.continuous.comp continuous_swap }
    refine ⟨TopCat.ofHom l,?_,?_⟩
    · ext x
      apply Subtype.ext
      apply Prod.ext
      · exact ContinuousMap.congr_fun hc x
      · apply ContinuousMap.ext
        intro t
        exact hA t x
    · ext x
      exact K.map_one_left x

/-- Actual HLP projections and full HELP of every original strict-fiber map
supply exact finite cube-boundary lifting of the vertical endpoint. -/
theorem endpoint_boundaryLifting_of_fiberHELP
    (p : C(E, B)) (q : C(F, B)) (f : C(E, F)) (sq : q.comp f = p)
    (hp : HomotopyLiftingProperty p) (hq : HomotopyLiftingProperty q)
    (hf : ∀ b : B,CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictMapOver p q f sq b)) :
    CubicalSubdivision.BoundaryLifting (endpoint q f) := by
  apply CubicalSubdivision.boundaryLifting_of_hasLiftingProperty
  intro n
  let : CompactSpace (CubicalTests.boundaryPresentation.{u} n).space :=
    (CubicalTests.boundaryPresentation n).compact
  let : CompactSpace (CubicalTests.boundary.{u} n) :=
    (CubicalTests.boundaryPresentationHomeomorph n).compactSpace
  apply endpoint_hasLiftingProperty_of_pairHELP q f
  intro a b H hH
  have hzero : ∀ x,CubicalTests.boundaryDuration n x = 0 ↔
      x ∈ Set.range (CubicalTests.boundaryInclusion.{u} n) := by
    intro x
    rw [CubicalTests.boundaryDuration_eq_zero_iff]
    exact ⟨fun hx ↦ ⟨⟨x,hx⟩,rfl⟩,fun ⟨y,hy⟩ ↦ hy ▸ y.property⟩
  obtain ⟨c,hc,_,K,hK,hA⟩ := fullHELP_over_contracted_test p q f sq hp hq hf _ _
    (CubicalTests.boundaryInclusion n) (CubicalTests.boundaryInclusion_hep n)
    (CubicalTests.zero n) (CubicalTests.contraction n) (CubicalTests.boundaryDuration n) hzero a
      b H hH
  exact ⟨c,hc,K,hK,hA⟩

end Topology.FiberwiseMappingPath
