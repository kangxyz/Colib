/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.ChainSupport

/-!
Adapted from `Quillen/Topology/LocalCoefficients/HomologySupport.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining its actual coefficient maps.

# Finite coefficient tests preserved by actual spatial pushforward

A finite support is chosen before the later map and coefficient conversion.
Its pointwise image therefore controls the transported class after stabilization.
-/

@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace FundamentalGroupoid.LocalCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {X : Type u} [TopologicalSpace X]

/-- A single finite point set controls all later pushforwards of a given class,
including arbitrary original coefficient conversion before the spatial map. -/
theorem homology_exists_finite_pushforward_test_set (A : System.{u, u} X)
    (n : ℕ) (x : homology A n) :
    ∃ s : Finset X, ∀ {Y : Type u} [TopologicalSpace Y]
      (f : C(X, Y)) (B D : System.{u, u} Y) (η : A ⟶ pullback f B) (α β : B ⟶ D),
      (∀ p ∈ s, α.app (FundamentalGroupoid.mk (f p)) =
        β.app (FundamentalGroupoid.mk (f p))) →
      coefficientHomologyMap α n
          (pushforwardHomologyMap f B n (coefficientHomologyMap η n x)) =
        coefficientHomologyMap β n
          (pushforwardHomologyMap f B n (coefficientHomologyMap η n x)) := by
  classical
  obtain ⟨s, hs⟩ := homology_exists_finite_test_set A n x
  refine ⟨s.image (fun σ ↦ σ (stdSimplex.vertex 0)), fun f B D η α β h ↦ ?_⟩
  have he := hs (pullback f D) (η ≫ pullbackMap f α) (η ≫ pullbackMap f β) (fun σ hσ ↦ ?_)
  · rw [coefficientHomologyMap_comp, coefficientHomologyMap_comp] at he
    have hα := congrArg (fun k ↦ k (coefficientHomologyMap η n x))
      (pushforwardHomologyMap_coefficient_naturality f α n)
    have hβ := congrArg (fun k ↦ k (coefficientHomologyMap η n x))
      (pushforwardHomologyMap_coefficient_naturality f β n)
    exact hα.symm.trans ((congrArg (pushforwardHomologyMap f D n) he).trans hβ)
  · change η.app _ ≫ α.app (FundamentalGroupoid.mk (f (σ (stdSimplex.vertex 0)))) =
      η.app _ ≫ β.app (FundamentalGroupoid.mk (f (σ (stdSimplex.vertex 0))))
    rw [h _ (Finset.mem_image.mpr ⟨σ, hσ, rfl⟩)]

end FundamentalGroupoid.LocalCoefficients
