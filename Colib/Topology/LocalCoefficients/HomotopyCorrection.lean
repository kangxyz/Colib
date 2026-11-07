/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.FiniteTrackDescent
public import Colib.Topology.LocalCoefficients.ChainSupport

/-!
Adapted from `Quillen/Topology/LocalCoefficients/HomotopyCorrection.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining its actual coefficient maps.

# Finite correction of two genuine homotopy transports

The groupoid correction is applied to the fundamental-groupoid transformations
of two specified continuous homotopies. Its finite-support homology consequence
retains the original homotopy-induced coefficient maps.
-/

@[expose] public section
noncomputable section
open CategoryTheory
open scoped Simplicial
universe u v w

namespace FundamentalGroupoid.LocalCoefficients

/-- Two actual homotopies admit one target coefficient correction on a finite
set whose component identifications are reflected by the common endpoint map. -/
theorem finite_homotopy_correction_exists {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {f g : C(X, Y)}
    (H K : f.Homotopy g) {A : System.{v, w} Y} (hA : AbelianMonodromy A)
    (s : Finset X)
    (hs : ∀ x ∈ s, ∀ y ∈ s, Joined (g x) (g y) → Joined x y) :
    ∃ T : A ≅ A, ∀ x ∈ s,
      transport A (H.evalAt x) ≫ T.hom.app (FundamentalGroupoid.mk (g x)) =
        transport A (K.evalAt x) := by
  classical
  let t := s.image FundamentalGroupoid.mk
  have ht : ∀ x ∈ t, ∀ y ∈ t,
      Nonempty ((FundamentalGroupoid.map g).obj x ⟶ (FundamentalGroupoid.map g).obj y) →
        Nonempty (x ⟶ y) := by
    intro x hx y hy h
    change x ∈ s.image FundamentalGroupoid.mk at hx
    change y ∈ s.image FundamentalGroupoid.mk at hy
    obtain ⟨a, ha, hax⟩ : ∃ a : X, a ∈ s ∧ FundamentalGroupoid.mk a = x :=
      Finset.mem_image.mp hx
    obtain ⟨b, hb, hby⟩ : ∃ b : X, b ∈ s ∧ FundamentalGroupoid.mk b = y :=
      Finset.mem_image.mp hy
    subst x y
    exact (nonempty_fundamental_hom_iff_joined a b).mpr
      (hs a ha b hb ((nonempty_fundamental_hom_iff_joined (g a) (g b)).mp h))
  obtain ⟨T, hT, _⟩ := finite_track_correction_exists
    (FundamentalGroupoidFunctor.homotopicMapsNatIso H)
    (FundamentalGroupoidFunctor.homotopicMapsNatIso K) hA t ht
  exact ⟨T, fun x hx ↦ hT (FundamentalGroupoid.mk x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)⟩

/-- For a fixed homology class only a finite component-reflection condition is
needed to correct the two original coefficient-transport maps. -/
theorem homology_finite_homotopy_correction {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] {f g : C(X, Y)}
    (H K : f.Homotopy g) {A : System.{u, u} Y} (hA : AbelianMonodromy A)
    (n : ℕ) (x : homology (pullback f A) n) :
    ∃ s : Finset X,
      (∀ a ∈ s, ∀ b ∈ s, Joined (g a) (g b) → Joined a b) →
      ∃ T : A ≅ A,
        coefficientHomologyMap (pullbackMap g T.hom) n
          (coefficientHomologyMap (homotopyPullbackIso H A).hom n x) =
        coefficientHomologyMap (homotopyPullbackIso K A).hom n x := by
  classical
  obtain ⟨s, hs⟩ := homology_exists_finite_test_set (pullback f A) n x
  refine ⟨s.image (fun σ ↦ σ (Convexity.StdSimplex.single 0)), fun h ↦ ?_⟩
  obtain ⟨T, hT⟩ := finite_homotopy_correction_exists H K hA _ h
  refine ⟨T, ?_⟩
  have he := hs (pullback g A)
    ((homotopyPullbackIso H A).hom ≫ pullbackMap g T.hom)
    (homotopyPullbackIso K A).hom (fun σ hσ ↦
      hT (σ (Convexity.StdSimplex.single 0)) (Finset.mem_image.mpr ⟨σ, hσ, rfl⟩))
  rw [coefficientHomologyMap_comp] at he
  exact he

end FundamentalGroupoid.LocalCoefficients
