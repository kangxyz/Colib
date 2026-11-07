/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HELP.CubeBoundaryHomeomorph

/-!
# The literal cubical horn and top-face attachment

The horn consists of the side faces and bottom face. It contracts by lowering
the last coordinate and then contracting the bottom cube. The top face and
horn give a genuine compact Hausdorff quotient presentation of the whole
boundary, hence an actual pushout and a genuine horn inclusion HEP.


Implementation provenance:
`Quillen/Topology/HELP/CubicalHorn.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open Topology

noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits
open scoped Topology unitInterval
universe u
namespace Topology.CubicalTests

/-- Side faces together with the bottom face, in original product coordinates. -/
abbrev Horn (n : ℕ) :=
  {z : cube.{u} n × unitInterval // z.1.down ∈ Cube.boundary (Fin n) ∨ z.2 = 0}

/-- The whole boundary of the product cube, in the same coordinates. -/
abbrev ProductBoundary (n : ℕ) :=
  {z : cube.{u} n × unitInterval //
    z.1.down ∈ Cube.boundary (Fin n) ∨ z.2 = 0 ∨ z.2 = 1}

private theorem closed_boundarySet (n : ℕ) :
    IsClosed {z : cube.{u} n | z.down ∈ Cube.boundary (Fin n)} := by
  change IsClosed {z : cube.{u} n | ∃ i : Fin n,z.down i = 0 ∨ z.down i = 1}
  simpa only [Set.ofPred_exists,Set.ofPred_or] using
    (isClosed_iUnion_of_finite fun i : Fin n ↦
      (isClosed_eq (by fun_prop : Continuous (fun z : cube.{u} n ↦ z.down i))
        continuous_const).union (isClosed_eq (by fun_prop) continuous_const))

private theorem closed_hornSet (n : ℕ) :
    IsClosed {z : cube.{u} n × unitInterval |
      z.1.down ∈ Cube.boundary (Fin n) ∨ z.2 = 0} :=
  ((closed_boundarySet n).preimage continuous_fst).union
    (isClosed_eq continuous_snd continuous_const)

instance horn_compactSpace (n : ℕ) : CompactSpace (Horn.{u} n) :=
  isCompact_iff_compactSpace.mp (closed_hornSet n).isCompact

/-- The literal inclusion of the horn in the whole boundary. -/
def hornInclusion (n : ℕ) : TopCat.of (Horn.{u} n) ⟶ TopCat.of (ProductBoundary.{u} n) :=
  TopCat.ofHom ⟨fun z ↦ ⟨z.val,z.property.elim Or.inl (Or.inr ∘ Or.inl)⟩,by fun_prop⟩

/-- The top face, with no quotient or reparametrization. -/
def topFace (n : ℕ) : cube.{u} n ⟶ TopCat.of (ProductBoundary.{u} n) :=
  TopCat.ofHom ⟨fun x ↦ ⟨(x,1),Or.inr (Or.inr rfl)⟩,by fun_prop⟩

/-- The top rim viewed in the side of the horn. -/
def topRim (n : ℕ) : TopCat.of (boundary.{u} n) ⟶ TopCat.of (Horn.{u} n) :=
  TopCat.ofHom ⟨fun x ↦ ⟨(x.val,1),Or.inl x.property⟩,by fun_prop⟩

theorem hornTop_square (n : ℕ) :
    boundaryInclusion n ≫ topFace n = topRim n ≫ hornInclusion n := rfl

/-- The bottom origin, also present for the zero-dimensional cube. -/
def hornZero (n : ℕ) : Horn.{u} n := ⟨(zero n,0),Or.inr rfl⟩

/-- Project the horn to its bottom face. -/
def hornBottom (n : ℕ) : C(Horn.{u} n,Horn.{u} n) :=
  ⟨fun z ↦ ⟨(z.val.1,0),Or.inr rfl⟩,by fun_prop⟩

/-- Lower only the interval coordinate, staying inside the original horn. -/
def hornLower (n : ℕ) : (ContinuousMap.id (Horn.{u} n)).Homotopy (hornBottom n) where
  toFun z := ⟨(z.2.val.1,unitInterval.symm z.1 * z.2.val.2),by
    rcases z.2.property with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h,mul_zero])⟩
  continuous_toFun := by fun_prop
  map_zero_left z := by apply Subtype.ext; exact Prod.ext rfl (by simp)
  map_one_left z := by apply Subtype.ext; exact Prod.ext rfl (by simp [hornBottom])

/-- Contract the bottom face of the horn to its zero vertex. -/
def hornBottomContraction (n : ℕ) : (hornBottom n).Homotopy
    (ContinuousMap.const _ (hornZero n)) where
  toFun z := ⟨(contraction n (z.1,z.2.val.1),0),Or.inr rfl⟩
  continuous_toFun := by fun_prop
  map_zero_left z := by
    apply Subtype.ext
    exact Prod.ext ((contraction n).map_zero_left z.val.1) rfl
  map_one_left z := by
    apply Subtype.ext
    exact Prod.ext ((contraction n).map_one_left z.val.1) rfl

/-- A genuine contraction of the actual horn, in every finite dimension. -/
def hornContraction (n : ℕ) : (ContinuousMap.id (Horn.{u} n)).Homotopy
    (ContinuousMap.const _ (hornZero n)) :=
  (hornLower n).trans (hornBottomContraction n)

/-- The original sum of the top face and horn covers the whole boundary. -/
theorem hornTop_surjective (n : ℕ) :
    Function.Surjective (Sum.elim (topFace.{u} n) (hornInclusion n)) := by
  intro z
  rcases z.property with hx | ht | ht
  · exact ⟨Sum.inr ⟨z.val,Or.inl hx⟩,rfl⟩
  · exact ⟨Sum.inr ⟨z.val,Or.inr ht⟩,rfl⟩
  · exact ⟨Sum.inl z.val.1,Subtype.ext (Prod.ext rfl ht.symm)⟩

/-- Compact Hausdorff quotient descent for the literal top/horn cover. -/
theorem hornTop_isQuotientMap (n : ℕ) :
    IsQuotientMap (Sum.elim (topFace.{u} n) (hornInclusion n)) :=
  IsQuotientMap.of_surjective_continuous (hornTop_surjective n)
    ((topFace n).hom.continuous.sumElim (hornInclusion n).hom.continuous)

section Desc
variable {n : ℕ} {Z : TopCat.{u}} (b : cube.{u} n ⟶ Z)
  (h : TopCat.of (Horn.{u} n) ⟶ Z)
  (w : boundaryInclusion n ≫ b = topRim n ≫ h)

/-- The set-level gluing of the top-face map and horn map on the product boundary. -/
def hornTopDescFun (z : ProductBoundary.{u} n) : Z := by
  classical
  exact if hz : z.val.1.down ∈ Cube.boundary (Fin n) ∨ z.val.2 = 0
    then h ⟨z.val,hz⟩ else b z.val.1

private theorem hornTopDescFun_horn (z : Horn.{u} n) :
    hornTopDescFun b h (hornInclusion n z) = h z := by
  classical
  simp [hornTopDescFun,hornInclusion,z.property]

include w in
private theorem hornTopDescFun_top (z : cube.{u} n) :
    hornTopDescFun b h (topFace n z) = b z := by
  classical
  by_cases hz : z.down ∈ Cube.boundary (Fin n)
  · simpa [hornTopDescFun,topFace,hz,topRim,boundaryInclusion] using
      (ConcreteCategory.congr_hom w ⟨z,hz⟩).symm
  · simp [hornTopDescFun,topFace,hz,one_ne_zero]

/-- Pasting uses the genuine quotient cover and agreement on its original rim. -/
def hornTopDesc : TopCat.of (ProductBoundary.{u} n) ⟶ Z := TopCat.ofHom
  ⟨hornTopDescFun b h,by
    apply (hornTop_isQuotientMap n).continuous_iff.2
    have hh : hornTopDescFun b h ∘ Sum.elim (topFace n) (hornInclusion n) =
        Sum.elim b h := by
      funext z
      cases z with
      | inl z => exact hornTopDescFun_top b h w z
      | inr z => exact hornTopDescFun_horn b h z
    rw [hh]
    exact b.hom.continuous.sumElim h.hom.continuous⟩

@[simp] theorem topFace_desc : topFace n ≫ hornTopDesc b h w = b := by
  ext z : 1
  exact hornTopDescFun_top b h w z

@[simp] theorem hornInclusion_desc : hornInclusion n ≫ hornTopDesc b h w = h := by
  ext z : 1
  exact hornTopDescFun_horn b h z

end Desc

/-- The entire boundary is the actual top cube attached to the actual horn
along the original cube boundary. -/
theorem hornTop_isPushout (n : ℕ) :
    IsPushout (boundaryInclusion.{u} n) (topRim n) (topFace n) (hornInclusion n) := by
  apply IsPushout.of_isColimit (c := PushoutCocone.mk (topFace n) (hornInclusion n)
    (hornTop_square n))
  refine PushoutCocone.IsColimit.mk _
    (fun s ↦ hornTopDesc s.inl s.inr s.condition)
    (fun s ↦ topFace_desc s.inl s.inr s.condition)
    (fun s ↦ hornInclusion_desc s.inl s.inr s.condition) ?_
  intro s m hm₁ hm₂
  ext z : 1
  obtain ⟨z,rfl⟩ := hornTop_surjective n z
  cases z with
  | inl z =>
      exact (ConcreteCategory.congr_hom hm₁ z).trans
        (ConcreteCategory.congr_hom (topFace_desc s.inl s.inr s.condition) z).symm
  | inr z =>
      exact (ConcreteCategory.congr_hom hm₂ z).trans
        (ConcreteCategory.congr_hom (hornInclusion_desc s.inl s.inr s.condition) z).symm

/-- Horn inclusion HEP is the genuine cobase change of cube-boundary HEP. -/
theorem hornInclusion_hep (n : ℕ) :
    TopCat.HomotopyExtensionProperty (hornInclusion.{u} n) :=
  TopCat.homotopyExtensionProperty_pushout (hornTop_isPushout n) (boundaryInclusion_hep n)

/-- Product-coordinate whole boundary equals the actual next cube boundary. -/
def productBoundaryHomeomorph (n : ℕ) : ProductBoundary.{u} n ≃ₜ boundary.{u} (n+1) where
  toFun z := ⟨stepHomeomorph n z.val,by
    rcases z.property with ⟨i,hi⟩ | ht | ht
    · exact ⟨i.succ,hi⟩
    · exact ⟨0,Or.inl ht⟩
    · exact ⟨0,Or.inr ht⟩⟩
  invFun z := ⟨(stepHomeomorph n).symm z.val,by
    obtain ⟨i,hi⟩ := z.property
    cases i using Fin.cases with
    | zero => exact Or.inr hi
    | succ i => exact Or.inl ⟨i,hi⟩⟩
  left_inv z := Subtype.ext ((stepHomeomorph n).symm_apply_apply z.val)
  right_inv z := Subtype.ext ((stepHomeomorph n).apply_symm_apply z.val)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The unchanged boundary inclusion in product coordinates. -/
def productBoundaryInclusion (n : ℕ) :
    TopCat.of (ProductBoundary.{u} n) ⟶ TopCat.of (cube.{u} n × unitInterval) :=
  TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩

theorem productBoundaryInclusion_factor (n : ℕ) :
    (TopCat.isoOfHomeo (productBoundaryHomeomorph.{u} n)).hom ≫ boundaryInclusion (n+1) ≫
      (TopCat.isoOfHomeo (stepHomeomorph n)).inv = productBoundaryInclusion n := by
  ext z : 1
  exact (stepHomeomorph n).symm_apply_apply z.val

/-- Whole-boundary HEP uses only the literal next-cube coordinate homeomorphism. -/
theorem productBoundaryInclusion_hep (n : ℕ) :
    TopCat.HomotopyExtensionProperty (productBoundaryInclusion.{u} n) := by
  rw [← productBoundaryInclusion_factor]
  exact TopCat.homotopyExtensionProperty_comp (TopCat.homotopyExtensionProperty_of_isIso _)
    (TopCat.homotopyExtensionProperty_comp (boundaryInclusion_hep (n+1))
      (TopCat.homotopyExtensionProperty_of_isIso _))

end Topology.CubicalTests
