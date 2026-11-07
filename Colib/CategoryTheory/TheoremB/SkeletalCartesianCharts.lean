/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremA.SkeletalAttachments
public import Colib.CategoryTheory.TheoremA.SkeletalNaturality

/-!
# Characteristic charts into actual replacement restrictions

Characteristic charts are defined for every simplex, including degenerate
simplices, into any base subcomplex containing its image. Their face equations
retain the first-vertex transport in the coefficient. Eilenberg–Zilber then
reduces arbitrary charts to unique nondegenerate charts through an invertible
coefficient transition.
-/
/-! Implementation provenance: adapted from
`Quillen/CategoryTheory/TheoremB/SkeletalCartesianCharts.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd, retaining the actual replacement charts,
base restrictions and canonical comparisons. -/
@[expose] public section

open CategoryTheory.TheoremA SSet


noncomputable section
open CategoryTheory Limits Opposite
open scoped Simplicial Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.TheoremB.Skeletal
open TheoremA
variable {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})

/-- An enriched simplex chart with domain restricted to an actual subcomplex. -/
def restrictedSimplexChart (A : (nerve D).Subcomplex) {n : ℕ}
    (s : (nerve D).obj (op ⦋n⦌)) (K : (Δ[n] : SSet.{u}).Subcomplex)
    (hs : ∀ (p : SimplexCategoryᵒᵖ) (a : K.obj p),
      (nerve D).map a.1.down.op s ∈ A.obj p) :
    outerProduct K (H.obj (s.obj 0)) ⟶ replacementRestriction H A where
  app p := {
    app q := ↾fun x ↦ ⟨⟨(nerve D).map x.1.1.down.op s, hs p x.1⟩,
      (H.map (firstVertexEdge x.1.1.down.op s)).app q x.2⟩
    naturality q r β := by
      ext x : 3
      apply congrArg (Sigma.mk _)
      exact ConcreteCategory.congr_hom
        ((H.map (firstVertexEdge x.1.1.down.op s)).naturality β) x.2 }
  naturality p q α := by
    ext r x : 4
    change (⟨⟨(nerve D).map (x.1.1.down.op ≫ α) s, _⟩,
      (H.map (firstVertexEdge (x.1.1.down.op ≫ α) s)).app r x.2⟩ :
      ((replacementRestriction H A).obj q).obj r) = _
    rw [firstVertexEdge_comp, H.map_comp]
    rfl

/-- The full enriched characteristic chart of any simplex lying in a restriction. -/
def simplexChart (A : (nerve D).Subcomplex) {n : ℕ}
    (s : (nerve D).obj (op ⦋n⦌)) (hs : s ∈ A.obj (op ⦋n⦌)) :
    outerProduct Δ[n] (H.obj (s.obj 0)) ⟶ replacementRestriction H A where
  app p := {
    app q := ↾fun x ↦ ⟨⟨(nerve D).map x.1.down.op s, A.map x.1.down.op hs⟩,
      (H.map (firstVertexEdge x.1.down.op s)).app q x.2⟩
    naturality q r β := by
      ext x : 3
      apply congrArg (Sigma.mk _)
      exact ConcreteCategory.congr_hom
        ((H.map (firstVertexEdge x.1.down.op s)).naturality β) x.2 }
  naturality p q α := by
    ext r x : 4
    change (⟨⟨(nerve D).map (x.1.down.op ≫ α) s, _⟩,
      (H.map (firstVertexEdge (x.1.down.op ≫ α) s)).app r x.2⟩ :
      ((replacementRestriction H A).obj q).obj r) = _
    rw [firstVertexEdge_comp, H.map_comp]
    rfl

/-- Restriction of a full chart is precisely its subcomplex chart. -/
theorem simplexChart_restrict (A : (nerve D).Subcomplex) {n : ℕ}
    (s : (nerve D).obj (op ⦋n⦌)) (hs : s ∈ A.obj (op ⦋n⦌))
    (K : (Δ[n] : SSet.{u}).Subcomplex) :
    outerProductMap K.ι ≫ simplexChart H A s hs =
      restrictedSimplexChart H A s K (fun _ a ↦ A.map a.1.down.op hs) := rfl

/-- Enlarging the target restriction preserves the exact characteristic map. -/
theorem simplexChart_inclusion {A B : (nerve D).Subcomplex} (h : A ≤ B)
    {n : ℕ} (s : (nerve D).obj (op ⦋n⦌)) (hs : s ∈ A.obj (op ⦋n⦌)) :
    simplexChart H A s hs ≫ replacementRestrictionInclusion H h =
      simplexChart H B s (h _ hs) := rfl

/-- The existing enriched characteristic map is this actual chart. -/
theorem simplexChart_characteristic {n : ℕ} (s : (nerve D).nonDegenerate n) :
    simplexChart H ((nerve D).skeleton (n + 1)) s.1 ((nerve D).mem_skeleton s.1) =
      replacementCellCharacteristic H s := rfl

/-- The boundary chart is exactly the actual attaching map into the preceding skeleton. -/
theorem restrictedSimplexChart_attaching {n : ℕ} (s : (nerve D).nonDegenerate n) :
    restrictedSimplexChart H ((nerve D).skeleton n) s.1 ∂Δ[n]
      (fun _ a ↦ replacementBaseCell_boundary s a) = replacementCellAttaching H s := rfl

/-- Every simplex operator has its exact chart equation, including its
required first-vertex coefficient map. -/
theorem simplexChart_operator (A : (nerve D).Subcomplex) {n k : ℕ}
    (s : (nerve D).obj (op ⦋n⦌)) (hs : s ∈ A.obj (op ⦋n⦌))
    (α : ⦋k⦌ ⟶ ⦋n⦌) :
    outerProductMap (SSet.stdSimplex.map α) ≫ simplexChart H A s hs =
      outerProductCoefficientMap (H.map (firstVertexEdge α.op s)) ≫
        simplexChart H A ((nerve D).map α.op s) (A.map α.op hs) := by
  ext p q x : 5
  change (⟨⟨(nerve D).map (α.op ≫ x.1.down.op) s, _⟩,
    (H.map (firstVertexEdge (α.op ≫ x.1.down.op) s)).app q x.2⟩ :
    ((replacementRestriction H A).obj p).obj q) = _
  rw [firstVertexEdge_comp, H.map_comp]
  rfl

/-- The chart equations are natural in the coefficient diagram. -/
theorem simplexChart_coefficient {J : D ⥤ SSet.{u}} (η : H ⟶ J)
    (A : (nerve D).Subcomplex) {n : ℕ}
    (s : (nerve D).obj (op ⦋n⦌)) (hs : s ∈ A.obj (op ⦋n⦌)) :
    simplexChart H A s hs ≫ replacementRestrictionMap η A =
      outerProductCoefficientMap (η.app (s.obj 0)) ≫ simplexChart J A s hs := by
  ext p q x : 5
  apply congrArg (Sigma.mk _)
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (η.naturality (firstVertexEdge x.1.down.op s)) q) x.2

/-- A degenerate simplex has the same initial coefficient as its unique
nondegenerate ancestor, via an actual isomorphism. -/
def simplexChartEpiCoefficientIso {n k : ℕ} (α : ⦋n⦌ ⟶ ⦋k⦌) [Epi α]
    (s : (nerve D).obj (op ⦋k⦌)) :
    H.obj (s.obj 0) ≅ H.obj (((nerve D).map α.op s).obj 0) := by
  letI := TheoremA.firstVertexEdge_isIso_of_epi (D := D) α s
  exact asIso (H.map (firstVertexEdge α.op s))

/-- Unique nondegenerate presentation inside an arbitrary target restriction.
Membership descends to the ancestor by a section of its simplex epimorphism. -/
theorem exists_nondegenerate_in_restriction (A : (nerve D).Subcomplex)
    {n : ℕ} (s : (nerve D).obj (op ⦋n⦌)) (hs : s ∈ A.obj (op ⦋n⦌)) :
    ∃ (k : ℕ) (α : ⦋n⦌ ⟶ ⦋k⦌) (_ : Epi α) (t : (nerve D).nonDegenerate k),
      t.1 ∈ A.obj (op ⦋k⦌) ∧ (nerve D).map α.op t.1 = s := by
  obtain ⟨k, α, hα, t, rfl⟩ := (nerve D).exists_nonDegenerate s
  obtain ⟨⟨hsec⟩⟩ := isSplitEpi_of_epi α
  refine ⟨k, α, hα, t, ?_, rfl⟩
  have hh := A.map hsec.section_.op hs
  have heq : (nerve D).map hsec.section_.op ((nerve D).map α.op t.1) = t.1 := by
    change ((nerve D).map α.op ≫ (nerve D).map hsec.section_.op) t.1 = t.1
    rw [← (nerve D).map_comp, ← op_comp, hsec.id, op_id, (nerve D).map_id]
    rfl
  change (nerve D).map hsec.section_.op ((nerve D).map α.op t.1) ∈ A.obj (op ⦋k⦌) at hh
  simpa only [heq] using hh

end CategoryTheory.TheoremB.Skeletal
