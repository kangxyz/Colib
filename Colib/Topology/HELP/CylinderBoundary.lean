/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Homotopy.ExtensionContinuous

public import Colib.Topology.Homotopy.RelativeCylinder
public import Colib.Topology.Category.TopCat.CompactHausdorffPushout

/-! # The compact endpoint-relative cylinder boundary

The domain is the actual topological pushout of the side cylinder and the
 two endpoint copies. It makes sense for every HEP map, without assuming an
embedding. The relative square-extension theorem proves its HEP.


Implementation provenance:
`Quillen/Topology/HELP/CylinderBoundary.lean`
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
universe u
namespace TopCat

variable {A B : TopCat.{u}} (i : A ⟶ B)

/-- Include two copies of `A` at times zero and one in the cylinder `A × I`. -/
def CylinderBoundary.cylinderBoundaryEnds (A : TopCat.{u}) : TopCat.of (A ⊕ A) ⟶ TopCat.of (A ×
  unitInterval) :=
  TopCat.ofHom ⟨Sum.elim (fun a ↦ (a, 0)) (fun a ↦ (a, 1)),
    Continuous.sumElim (by fun_prop) (by fun_prop)⟩

/-- Apply the attaching map `i : A ⟶ B` separately to the two endpoint copies of `A`. -/
def CylinderBoundary.cylinderBoundarySumMap : TopCat.of (A ⊕ A) ⟶ TopCat.of (B ⊕ B) :=
  TopCat.ofHom ⟨Sum.map i i, i.hom.continuous.sumMap i.hom.continuous⟩

/-- The pushout joining the side cylinder `A × I` to the two caps `B ⊕ B` along their endpoint
copies of `A`; no embedding hypothesis on `i` is needed. -/
def CylinderBoundary : TopCat.{u} := pushout (TopCat.CylinderBoundary.cylinderBoundaryEnds A)
  (TopCat.CylinderBoundary.cylinderBoundarySumMap i)

/-- The side-cylinder leg of the pushout defining `TopCat.CylinderBoundary i`. -/
def CylinderBoundary.cylinderBoundarySide : TopCat.of (A × unitInterval) ⟶ TopCat.CylinderBoundary
  i :=
  pushout.inl _ _

/-- The two-cap leg of the pushout defining `TopCat.CylinderBoundary i`. -/
def CylinderBoundary.cylinderBoundaryCaps : TopCat.of (B ⊕ B) ⟶ TopCat.CylinderBoundary i :=
  pushout.inr _ _

/-- The map `A × I ⟶ B × I` applying `i` to the space coordinate and retaining time. -/
def CylinderBoundary.cylinderBoundarySideMap : TopCat.of (A × unitInterval) ⟶ TopCat.of (B ×
  unitInterval) :=
  TopCat.ofHom ⟨fun z ↦ (i z.1, z.2), by fun_prop⟩

/-- The map from the endpoint-relative cylinder boundary to `B × I`, induced by `i` on the side
cylinder and the endpoint inclusions on the caps. -/
def CylinderBoundary.cylinderBoundaryMap : TopCat.CylinderBoundary i ⟶ TopCat.of (B × unitInterval)
  :=
  pushout.desc (TopCat.CylinderBoundary.cylinderBoundarySideMap i)
    (TopCat.CylinderBoundary.cylinderBoundaryEnds B) (by
    ext x : 1
    cases x <;> rfl)

@[simp] theorem CylinderBoundary.cylinderBoundarySide_map :
    TopCat.CylinderBoundary.cylinderBoundarySide i ≫ TopCat.CylinderBoundary.cylinderBoundaryMap i
      = TopCat.CylinderBoundary.cylinderBoundarySideMap i :=
  pushout.inl_desc _ _ _

@[simp] theorem CylinderBoundary.cylinderBoundaryCaps_map :
    TopCat.CylinderBoundary.cylinderBoundaryCaps i ≫ TopCat.CylinderBoundary.cylinderBoundaryMap i
      = TopCat.CylinderBoundary.cylinderBoundaryEnds B :=
  pushout.inr_desc _ _ _

theorem CylinderBoundary.cylinderBoundary_isPushout : IsPushout
  (TopCat.CylinderBoundary.cylinderBoundaryEnds A)
    (TopCat.CylinderBoundary.cylinderBoundarySumMap i)
      (TopCat.CylinderBoundary.cylinderBoundarySide i)
      (TopCat.CylinderBoundary.cylinderBoundaryCaps i) :=
  IsPushout.of_hasPushout _ _

instance CylinderBoundary.cylinderBoundary_compactSpace [CompactSpace A] [CompactSpace B] :
    CompactSpace (TopCat.CylinderBoundary i) := compactSpace_pushout
      (TopCat.CylinderBoundary.cylinderBoundary_isPushout i)

/-- The whole boundary of the relative cylinder has HEP, including both
endpoint copies. The proof uses the actual pushout topology. -/
theorem CylinderBoundary.homotopyExtensionProperty_cylinderBoundaryMap
    (hi : TopCat.HomotopyExtensionProperty i) : TopCat.HomotopyExtensionProperty
      (TopCat.CylinderBoundary.cylinderBoundaryMap i) := by
  apply TopCat.homotopyExtensionProperty_of_continuous
  intro Z f H hzero
  let S : C((A × unitInterval) × unitInterval, Z) :=
    ⟨fun z ↦ H (z.2, TopCat.CylinderBoundary.cylinderBoundarySide i z.1), by fun_prop⟩
  let H₀ : C(B × unitInterval, Z) :=
    ⟨fun z ↦ H (z.2, TopCat.CylinderBoundary.cylinderBoundaryCaps i (Sum.inl z.1)), by fun_prop⟩
  let H₁ : C(B × unitInterval, Z) :=
    ⟨fun z ↦ H (z.2, TopCat.CylinderBoundary.cylinderBoundaryCaps i (Sum.inr z.1)), by fun_prop⟩
  have hside (a : A) (t : unitInterval) :
      TopCat.CylinderBoundary.cylinderBoundaryMap i (TopCat.CylinderBoundary.cylinderBoundarySide
        i (a, t)) = (i a, t) :=
    ConcreteCategory.congr_hom (TopCat.CylinderBoundary.cylinderBoundarySide_map i) (a, t)
  have hcap₀ (b : B) :
      TopCat.CylinderBoundary.cylinderBoundaryMap i (TopCat.CylinderBoundary.cylinderBoundaryCaps
        i (Sum.inl b)) = (b, 0) :=
    ConcreteCategory.congr_hom (TopCat.CylinderBoundary.cylinderBoundaryCaps_map i) (Sum.inl b)
  have hcap₁ (b : B) :
      TopCat.CylinderBoundary.cylinderBoundaryMap i (TopCat.CylinderBoundary.cylinderBoundaryCaps
        i (Sum.inr b)) = (b, 1) :=
    ConcreteCategory.congr_hom (TopCat.CylinderBoundary.cylinderBoundaryCaps_map i) (Sum.inr b)
  have hcomm₀ (a : A) : TopCat.CylinderBoundary.cylinderBoundarySide i (a, 0) =
      TopCat.CylinderBoundary.cylinderBoundaryCaps i (Sum.inl (i a)) :=
    ConcreteCategory.congr_hom (TopCat.CylinderBoundary.cylinderBoundary_isPushout i).w (Sum.inl a)
  have hcomm₁ (a : A) : TopCat.CylinderBoundary.cylinderBoundarySide i (a, 1) =
      TopCat.CylinderBoundary.cylinderBoundaryCaps i (Sum.inr (i a)) :=
    ConcreteCategory.congr_hom (TopCat.CylinderBoundary.cylinderBoundary_isPushout i).w (Sum.inr a)
  obtain ⟨K, hK₀, hKS, hK₀', hK₁'⟩ := TopCat.homotopyExtensionProperty_interval_square_extension
    hi f S H₀ H₁
    (fun a t ↦ (hzero _).trans (congrArg f (hside a t)))
    (fun b ↦ (hzero _).trans (congrArg f (hcap₀ b)))
    (fun b ↦ (hzero _).trans (congrArg f (hcap₁ b)))
    (fun a t ↦ congrArg (fun x ↦ H (t, x)) (hcomm₀ a))
    (fun a t ↦ congrArg (fun x ↦ H (t, x)) (hcomm₁ a))
  refine ⟨⟨fun z ↦ K (z.2, z.1), by fun_prop⟩, ?_, ?_⟩
  · rintro ⟨b, t⟩
    exact hK₀ b t
  · intro t x
    obtain ⟨x, rfl⟩ := pushout_sum_surjective (TopCat.CylinderBoundary.cylinderBoundary_isPushout
      i) x
    rcases x with ⟨a, s⟩ | (b | b)
    · change K (TopCat.CylinderBoundary.cylinderBoundaryMap i
        (TopCat.CylinderBoundary.cylinderBoundarySide i (a, s)), t) = _
      rw [hside]
      exact hKS a s t
    · change K (TopCat.CylinderBoundary.cylinderBoundaryMap i
        (TopCat.CylinderBoundary.cylinderBoundaryCaps i (Sum.inl b)), t) = _
      rw [hcap₀]
      exact hK₀' b t
    · change K (TopCat.CylinderBoundary.cylinderBoundaryMap i
        (TopCat.CylinderBoundary.cylinderBoundaryCaps i (Sum.inr b)), t) = _
      rw [hcap₁]
      exact hK₁' b t

end TopCat
