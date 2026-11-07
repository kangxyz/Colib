/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.CubicalSubdivision.BoundaryLifting
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalenceProperty

/-! # Original weak equivalence from genuine finite cube-boundary lifting

The proof uses only literal n-cube and (n+1)-cube lifting. The latter supplies
homotopies of original generalized loops with their complete boundaries fixed.
No lifting property for arbitrary compact pairs is inferred.


Implementation provenance:
`Quillen/Topology/CubicalSubdivision/BoundaryWeakEquivalence.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits
open scoped Topology unitInterval
universe u v w
namespace Topology.CubicalSubdivision
variable {E : Type u} {F : Type v} [TopologicalSpace E] [TopologicalSpace F]
  {f : C(E, F)}

/-- The empty boundary of the actual zero-cube gives strict point-surjectivity. -/
theorem BoundaryLifting.surjective (hf : BoundaryLifting f) : Function.Surjective f := by
  intro y
  let : IsEmpty (Boundary 0) := ⟨fun t ↦ by obtain ⟨i,_⟩ := t.property; exact Fin.elim0 i⟩
  let a : C(Boundary 0,E) := ⟨isEmptyElim,continuous_of_discreteTopology⟩
  obtain ⟨c,_,hc⟩ := hf 0 a (ContinuousMap.const _ y) (fun t ↦ isEmptyElim t)
  exact ⟨c (fun i ↦ Fin.elim0 i),ContinuousMap.congr_fun hc (fun i ↦ Fin.elim0 i)⟩

/-- Transport only the test parameters along the actual boundary homeomorphism.
The source and target spaces retain their independent universes. -/
theorem BoundaryLifting.presentation (hf : BoundaryLifting f) (n : ℕ)
    (a : C((CubicalTests.boundaryPresentation.{w} n).space, E))
    (b : C(CubicalTests.cube.{w} n, F))
    (hab : ∀ z, f (a z) = b ((CubicalTests.boundaryPresentation n).map z)) :
    ∃ c : C(CubicalTests.cube.{w} n,E),
      (∀ z,c ((CubicalTests.boundaryPresentation n).map z) = a z) ∧ f.comp c = b := by
  let P := CubicalTests.boundaryPresentation.{w} n
  let e := CubicalTests.boundaryPresentationHomeomorph.{w} n
  let a' : C(Boundary n,E) := ⟨fun t ↦ a (e.symm ⟨⟨t.val⟩,t.property⟩),by fun_prop⟩
  let b' : C(Cube n,F) := ⟨fun t ↦ b ⟨t⟩,by fun_prop⟩
  have hab' (t : Boundary n) : f (a' t) = b' t := by
    have h := hab (e.symm ⟨⟨t.val⟩,t.property⟩)
    change f (a (e.symm ⟨⟨t.val⟩,t.property⟩)) = b ⟨t.val⟩
    rw [CubicalTests.boundaryPresentationHomeomorph_symm_map] at h
    exact h
  obtain ⟨c,hc,he⟩ := hf n a' b' hab'
  refine ⟨⟨fun z ↦ c z.down,by fun_prop⟩,?_,?_⟩
  · intro z
    have h := hc ⟨(P.map z).down,P.lands z⟩
    change c (P.map z).down = a (e.symm (e z)) at h
    change c (P.map z).down = a z
    simpa only [Homeomorph.symm_apply_apply] using h
  · ext z
    exact ContinuousMap.congr_fun he z.down

/-- The actual relative cylinder-boundary test is the next canonical cube
boundary, via the existing literal first-coordinate homeomorphism. -/
theorem BoundaryLifting.cylinder (hf : BoundaryLifting f) (n : ℕ)
    (a : C(TopCat.CylinderBoundary (CubicalTests.boundaryPresentation.{w} n).map, E))
    (b : C(CubicalTests.cube.{w} n × unitInterval, F))
    (hab : ∀ z, f (a z) = b (TopCat.CylinderBoundary.cylinderBoundaryMap
      (CubicalTests.boundaryPresentation n).map z)) :
    ∃ c : C(CubicalTests.cube.{w} n × unitInterval,E),
      (∀ z,c (TopCat.CylinderBoundary.cylinderBoundaryMap (CubicalTests.boundaryPresentation n).map
        z) = a z) ∧
        f.comp c = b := by
  let e := CubicalTests.stepHomeomorph.{w} n
  let b' := b.comp ⟨e.symm,e.symm.continuous⟩
  have hab' (z : (CubicalTests.boundaryPresentation.{w} (n+1)).space) :
      f (a z) = b' ((CubicalTests.boundaryPresentation (n+1)).map z) := by
    change f (a z) = b (e.symm (e (TopCat.CylinderBoundary.cylinderBoundaryMap
      (CubicalTests.boundaryPresentation n).map
      z)))
    rw [Homeomorph.symm_apply_apply]
    exact hab z
  obtain ⟨c,hc,he⟩ := hf.presentation (n+1) a b' hab'
  refine ⟨c.comp ⟨e,e.continuous⟩,fun z ↦ hc z,?_⟩
  ext z
  exact (ContinuousMap.congr_fun he (e z)).trans (congrArg b (e.symm_apply_apply z))

/-- Strict lifting gives surjectivity of the original quotient map in every
finite degree, including the ungrouped zero-dimensional homotopy set. -/
theorem BoundaryLifting.homotopy_surjective (hf : BoundaryLifting f) (x : E) (n : ℕ) :
    Function.Surjective (HomotopyGroup.map (N := Fin n) f (x := x) rfl) := by
  intro a
  induction a using Quotient.inductionOn with | h p =>
    obtain ⟨c,hc,he⟩ := hf n (ContinuousMap.const _ x) p.val
      (fun t ↦ (GenLoop.boundary p t.val t.property).symm)
    let q : GenLoop (Fin n) E x := ⟨c,fun t ht ↦ hc ⟨t,ht⟩⟩
    refine ⟨Quotient.mk' q,?_⟩
    rw [HomotopyGroup.map_mk]
    apply congrArg Quotient.mk'
    apply Subtype.ext
    exact he

/-- The strict (n+1)-cube lift is a genuine homotopy of the original n-loop
representatives, with their entire original boundaries fixed. -/
theorem BoundaryLifting.homotopy_injective (hf : BoundaryLifting f) (x : E) (n : ℕ) :
    Function.Injective (HomotopyGroup.map (N := Fin n) f (x := x) rfl) := by
  intro a b hab
  induction a using Quotient.inductionOn with | h p =>
    induction b using Quotient.inductionOn with | h q =>
      obtain ⟨H⟩ := Quotient.exact hab
      let P := CubicalTests.boundaryPresentation.{u} n
      let S : TopCat.of (P.space × unitInterval) ⟶ TopCat.of E :=
        TopCat.ofHom (ContinuousMap.const _ x)
      let caps : TopCat.of (CubicalTests.cube.{u} n ⊕ CubicalTests.cube.{u} n) ⟶ TopCat.of E :=
        TopCat.ofHom ⟨Sum.elim (fun z ↦ p z.down) (fun z ↦ q z.down),
          (p.val.continuous.comp continuous_uliftDown).sumElim
            (q.val.continuous.comp continuous_uliftDown)⟩
      have w : TopCat.CylinderBoundary.cylinderBoundaryEnds P.space ≫ S =
        TopCat.CylinderBoundary.cylinderBoundarySumMap P.map ≫ caps := by
        ext z
        rcases z with a | a
        · exact (GenLoop.boundary p (P.map a).down (P.lands a)).symm
        · exact (GenLoop.boundary q (P.map a).down (P.lands a)).symm
      let d : TopCat.CylinderBoundary P.map ⟶ TopCat.of E := pushout.desc S caps w
      have hS : TopCat.CylinderBoundary.cylinderBoundarySide P.map ≫ d = S := pushout.inl_desc _ _
        _
      have hcaps : TopCat.CylinderBoundary.cylinderBoundaryCaps P.map ≫ d = caps :=
        pushout.inr_desc _ _ _
      let k : C(CubicalTests.cube.{u} n × unitInterval,F) :=
        ⟨fun z ↦ H (z.2,z.1.down),H.continuous.comp
          (continuous_snd.prodMk (continuous_uliftDown.comp continuous_fst))⟩
      have hw (z : TopCat.CylinderBoundary P.map) : f (d z) = k
        (TopCat.CylinderBoundary.cylinderBoundaryMap P.map z) := by
        obtain ⟨z,rfl⟩ := pushout_sum_surjective
          (TopCat.CylinderBoundary.cylinderBoundary_isPushout P.map) z
        rcases z with ⟨a,t⟩ | (z | z)
        · change f (d (TopCat.CylinderBoundary.cylinderBoundarySide P.map (a,t))) =
            k (TopCat.CylinderBoundary.cylinderBoundaryMap P.map
              (TopCat.CylinderBoundary.cylinderBoundarySide P.map (a,t)))
          have hd : d (TopCat.CylinderBoundary.cylinderBoundarySide P.map (a,t)) = x :=
            ConcreteCategory.congr_hom hS (a,t)
          have hj : TopCat.CylinderBoundary.cylinderBoundaryMap P.map
            (TopCat.CylinderBoundary.cylinderBoundarySide P.map (a,t)) = (P.map a,t) :=
            ConcreteCategory.congr_hom (TopCat.CylinderBoundary.cylinderBoundarySide_map P.map)
              (a,t)
          rw [hd,hj]
          exact ((H.eq_fst t (P.lands a)).trans
            (congrArg f (GenLoop.boundary p (P.map a).down (P.lands a)))).symm
        · change f (d (TopCat.CylinderBoundary.cylinderBoundaryCaps P.map (Sum.inl z))) =
            k (TopCat.CylinderBoundary.cylinderBoundaryMap P.map
              (TopCat.CylinderBoundary.cylinderBoundaryCaps P.map (Sum.inl z)))
          have hd : d (TopCat.CylinderBoundary.cylinderBoundaryCaps P.map (Sum.inl z)) = p z.down
            :=
            ConcreteCategory.congr_hom hcaps (Sum.inl z)
          have hj : TopCat.CylinderBoundary.cylinderBoundaryMap P.map
            (TopCat.CylinderBoundary.cylinderBoundaryCaps P.map (Sum.inl z)) = (z,0) :=
            ConcreteCategory.congr_hom (TopCat.CylinderBoundary.cylinderBoundaryCaps_map P.map)
              (Sum.inl z)
          rw [hd,hj]
          exact (H.apply_zero z.down).symm
        · change f (d (TopCat.CylinderBoundary.cylinderBoundaryCaps P.map (Sum.inr z))) =
            k (TopCat.CylinderBoundary.cylinderBoundaryMap P.map
              (TopCat.CylinderBoundary.cylinderBoundaryCaps P.map (Sum.inr z)))
          have hd : d (TopCat.CylinderBoundary.cylinderBoundaryCaps P.map (Sum.inr z)) = q z.down
            :=
            ConcreteCategory.congr_hom hcaps (Sum.inr z)
          have hj : TopCat.CylinderBoundary.cylinderBoundaryMap P.map
            (TopCat.CylinderBoundary.cylinderBoundaryCaps P.map (Sum.inr z)) = (z,1) :=
            ConcreteCategory.congr_hom (TopCat.CylinderBoundary.cylinderBoundaryCaps_map P.map)
              (Sum.inr z)
          rw [hd,hj]
          exact (H.apply_one z.down).symm
      obtain ⟨c,hc,_⟩ := hf.cylinder n d.hom k hw
      have hside (a : P.space) (t : unitInterval) : c (P.map a,t) = x := by
        have he := hc (TopCat.CylinderBoundary.cylinderBoundarySide P.map (a,t))
        have hs := ConcreteCategory.congr_hom (TopCat.CylinderBoundary.cylinderBoundarySide_map
          P.map) (a,t)
        have hd := ConcreteCategory.congr_hom hS (a,t)
        exact (congrArg c hs).symm.trans (he.trans hd)
      have hzero (z : CubicalTests.cube.{u} n) : c (z,0) = p z.down := by
        have he := hc (TopCat.CylinderBoundary.cylinderBoundaryCaps P.map (Sum.inl z))
        have hs := ConcreteCategory.congr_hom (TopCat.CylinderBoundary.cylinderBoundaryCaps_map
          P.map) (Sum.inl z)
        have hd := ConcreteCategory.congr_hom hcaps (Sum.inl z)
        exact (congrArg c hs).symm.trans (he.trans hd)
      have hone (z : CubicalTests.cube.{u} n) : c (z,1) = q z.down := by
        have he := hc (TopCat.CylinderBoundary.cylinderBoundaryCaps P.map (Sum.inr z))
        have hs := ConcreteCategory.congr_hom (TopCat.CylinderBoundary.cylinderBoundaryCaps_map
          P.map) (Sum.inr z)
        have hd := ConcreteCategory.congr_hom hcaps (Sum.inr z)
        exact (congrArg c hs).symm.trans (he.trans hd)
      apply Quotient.sound
      refine ⟨{
        toHomotopy := {
          toFun z := c (ULift.up z.2,z.1)
          continuous_toFun := c.continuous.comp
            ((continuous_uliftUp.comp continuous_snd).prodMk continuous_fst)
          map_zero_left z := hzero (ULift.up z)
          map_one_left z := hone (ULift.up z) }
        prop' := ?_ }⟩
      intro t z hz
      obtain ⟨a,ha⟩ := P.covers (ULift.up z) hz
      change c (ULift.up z,t) = p z
      rw [← ha]
      exact (hside a t).trans (GenLoop.boundary p z hz).symm

/-- The empty-aware weak property is about the original map, with every
original finite homotopy-set map and no group law assumed in degree zero. -/
theorem BoundaryLifting.isWeakHomotopyEquivalence (hf : BoundaryLifting f) :
    IsWeakHomotopyEquivalence f where
  component_surjective y := by
    obtain ⟨x,hx⟩ := hf.surjective y
    refine ⟨x,?_⟩
    rw [hx]
  homotopy_bijective x n := ⟨hf.homotopy_injective x n,hf.homotopy_surjective x n⟩

end Topology.CubicalSubdivision
