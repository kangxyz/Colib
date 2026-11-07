/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyPullback.Coproducts
public import Colib.Topology.HomotopyPullback.Symmetry
public import Mathlib.Topology.ContinuousMap.Sigma

/-! # Path-space restriction to a coproduct component

A path in a topological coproduct stays in a single summand. Thus the
homotopy pullback along a map into one summand is homeomorphic to the
homotopy pullback formed entirely inside that summand. No summand is
assumed discrete and no map is assumed to be a fibration.
-/
/-! Implementation source: `Quillen/Topology/Realization/Cartesian/CoproductPaths.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual coproduct topologies and canonical
constant-path comparisons are retained. -/
@[expose] public section

open Topology

noncomputable section
open CategoryTheory Limits
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Topology.HomotopyPullback

variable {ι : Type u} {X B : ι → Type u} [∀ i, TopologicalSpace (X i)]
  [∀ i, TopologicalSpace (B i)] {A : Type u} [TopologicalSpace A]
  (q : ∀ i, C(X i, B i)) (k : ι) (g : C(A, B k))

/-- Include a homotopy pullback into the actual coproduct, including its
path coordinate by postcomposition with the target summand inclusion. -/
def componentPullbackMap : C(HomotopyPullback (q k) g,
    HomotopyPullback (sigmaMap q) ((ContinuousMap.sigmaMk k).comp g)) where
  toFun z := ⟨(z.1.1, ⟨k, z.1.2.1⟩, (ContinuousMap.sigmaMk k).comp z.1.2.2),
    congrArg (Sigma.mk k) z.2.1, congrArg (Sigma.mk k) z.2.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_sigmaMk.comp (continuous_fst.comp (continuous_snd.comp
        continuous_subtype_val))).prodMk
        ((ContinuousMap.sigmaMk k).continuous_postcomp.comp
          (continuous_snd.comp (continuous_snd.comp continuous_subtype_val))))

/-- Actual compact-open path-space homotopy pullbacks restrict
homeomorphically to one open coproduct component. -/
def componentPullbackHomeomorph : HomotopyPullback (q k) g ≃ₜ
    HomotopyPullback (sigmaMap q) ((ContinuousMap.sigmaMk k).comp g) := by
  have hind : IsInducing (componentPullbackMap q k g) := by
    exact ((IsInducing.id.prodMap ((IsEmbedding.sigmaMk (i := k)).isInducing.prodMap
      ((ContinuousMap.sigmaMk k).isInducing_postcomp IsEmbedding.sigmaMk.isInducing))).comp
      (show IsInducing (Subtype.val : HomotopyPullback (q k) g → A × (X k × C(unitInterval, B k)))
        from IsInducing.subtypeVal)).codRestrict
      (s := {z : A × ((Σ i, X i) × C(unitInterval, Σ i, B i)) |
        z.2.2 0 = sigmaMap q z.2.1 ∧ z.2.2 1 = ((ContinuousMap.sigmaMk k).comp g) z.1})
      (fun z ↦ (componentPullbackMap q k g z).2)
  have hinj : Function.Injective (componentPullbackMap q k g) := by
    intro z w h
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z ↦ z.1.1) h
    · apply Prod.ext
      · exact eq_of_heq (Sigma.mk.inj (congrArg (fun z ↦ z.1.2.1) h)).2
      · apply ContinuousMap.ext
        intro t
        exact eq_of_heq (Sigma.mk.inj (congrArg (fun z ↦ z.1.2.2 t) h)).2
  apply (IsEmbedding.mk hind hinj).toHomeomorphOfSurjective
  rintro ⟨⟨a, ⟨i, x⟩, p⟩, h0, h1⟩
  obtain ⟨j, r, rfl⟩ := p.exists_lift_sigma
  have hj : j = k := congrArg Sigma.fst h1
  subst j
  have hi : k = i := congrArg Sigma.fst h0
  subst i
  refine ⟨⟨(a, x, r), eq_of_heq (Sigma.mk.inj h0).2, eq_of_heq (Sigma.mk.inj h1).2⟩, ?_⟩
  rfl

@[simp] theorem componentPullbackHomeomorph_toMap :
    (componentPullbackHomeomorph q k g : C(_, _)) = componentPullbackMap q k g := rfl

/-- The canonical component-inclusion comparison is an actual homotopy
 equivalence, for every family of maps, without a fibration hypothesis. -/
def componentInclusionHomotopyEquiv : ContinuousMap.HomotopyEquiv (X k)
    (HomotopyPullback (sigmaMap q) (ContinuousMap.sigmaMk k)) :=
  ((HomotopyPullback.identityHomotopyEquiv (q k)).trans
    (HomotopyPullback.symmetryHomeomorph (ContinuousMap.id (B k)) (q k)).toHomotopyEquiv).trans
      (componentPullbackHomeomorph q k (ContinuousMap.id (B k))).toHomotopyEquiv

@[simp] theorem componentInclusionHomotopyEquiv_toFun :
    (componentInclusionHomotopyEquiv q k).toFun =
      HomotopyPullback.comparison (sigmaMap q) (ContinuousMap.sigmaMk k)
        (q k) (ContinuousMap.sigmaMk k) rfl := rfl

/-- The square formed by corresponding coproduct summand inclusions is
canonically homotopy cartesian in the actual compact-open path-space model. -/
theorem cartesianComponentInclusion :
    Cartesian (q k) (sigmaMap q) (ContinuousMap.sigmaMk k) (ContinuousMap.sigmaMk k) rfl :=
  ⟨componentInclusionHomotopyEquiv q k, rfl⟩

end Topology.HomotopyPullback
