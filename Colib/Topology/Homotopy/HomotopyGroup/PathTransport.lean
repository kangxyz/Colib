/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalence
public import Colib.Topology.Homotopy.FreePath

/-!
# Basepoint transport on the actual finite homotopy sets

Implementation provenance: the based transport part of
`Quillen/Topology/HomotopyGroups/PathTransport.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Existing free-path evaluations are reused.

Evaluation at any point of the interval is a genuine homotopy equivalence
from the free path space to the original space.  At the basepoint given by a
path, its endpoint evaluations therefore give transport in every finite
degree, including degree zero.  Naturality uses actual postcomposition of
free paths and the strict evaluation squares.
-/
@[expose] public section

noncomputable section
open scoped Topology unitInterval
universe u v
namespace Topology
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

variable {x₀ x₁ : X}

/-- The equivalence induced by the actual initial evaluation, based at `γ`. -/
def pathStartEquiv (γ : Path x₀ x₁) (n : ℕ) :
    HomotopyGroup.Pi n C(unitInterval, X) γ.toContinuousMap ≃ HomotopyGroup.Pi n X x₀ :=
  Equiv.ofBijective (HomotopyGroup.map (freePathEvaluation X 0) γ.source)
    (homotopyGroupMap_bijective_of_homotopyEquiv
      (freePathEvaluationHomotopyEquiv X 0) γ.source n)

/-- The equivalence induced by the actual terminal evaluation, based at `γ`. -/
def pathEndEquiv (γ : Path x₀ x₁) (n : ℕ) :
    HomotopyGroup.Pi n C(unitInterval, X) γ.toContinuousMap ≃ HomotopyGroup.Pi n X x₁ :=
  Equiv.ofBijective (HomotopyGroup.map (freePathEvaluation X 1) γ.target)
    (homotopyGroupMap_bijective_of_homotopyEquiv
      (freePathEvaluationHomotopyEquiv X 1) γ.target n)

/-- Transport along a path on the original finite homotopy sets.  This includes
`n = 0`; no group structure on the zeroth homotopy set is used. -/
def pathTransport (γ : Path x₀ x₁) (n : ℕ) :
    HomotopyGroup.Pi n X x₀ ≃ HomotopyGroup.Pi n X x₁ :=
  (pathStartEquiv γ n).symm.trans (pathEndEquiv γ n)

@[simp]
theorem pathStartEquiv_apply (γ : Path x₀ x₁) (n : ℕ)
    (a : HomotopyGroup.Pi n C(unitInterval, X) γ.toContinuousMap) :
    pathStartEquiv γ n a = HomotopyGroup.map (freePathEvaluation X 0) γ.source a := rfl

@[simp]
theorem pathEndEquiv_apply (γ : Path x₀ x₁) (n : ℕ)
    (a : HomotopyGroup.Pi n C(unitInterval, X) γ.toContinuousMap) :
    pathEndEquiv γ n a = HomotopyGroup.map (freePathEvaluation X 1) γ.target a := rfl

/-- Transport identifies the two actual endpoint evaluation maps. -/
@[simp] theorem pathTransport_homotopyGroupMap_start (γ : Path x₀ x₁) (n : ℕ)
    (a : HomotopyGroup.Pi n C(unitInterval, X) γ.toContinuousMap) :
    pathTransport γ n (HomotopyGroup.map (freePathEvaluation X 0) γ.source a) =
      HomotopyGroup.map (freePathEvaluation X 1) γ.target a := (pathStartEquiv γ n).symm_apply_apply
        a |> congrArg (pathEndEquiv γ n)

/-- The initial endpoint square for actual path postcomposition. -/
theorem pathStartEquiv_postcomp (f : C(X, Y)) (γ : Path x₀ x₁) (n : ℕ)
    (a : HomotopyGroup.Pi n C(unitInterval, X) γ.toContinuousMap) :
    pathStartEquiv (γ.map f.continuous) n
      (HomotopyGroup.map (freePathPostcomp f) rfl a) =
        HomotopyGroup.map f rfl (pathStartEquiv γ n a) := by
  induction a using Quotient.inductionOn with | h a => rfl

/-- The terminal endpoint square for actual path postcomposition. -/
theorem pathEndEquiv_postcomp (f : C(X, Y)) (γ : Path x₀ x₁) (n : ℕ)
    (a : HomotopyGroup.Pi n C(unitInterval, X) γ.toContinuousMap) :
    pathEndEquiv (γ.map f.continuous) n
      (HomotopyGroup.map (freePathPostcomp f) rfl a) =
        HomotopyGroup.map f rfl (pathEndEquiv γ n a) := by
  induction a using Quotient.inductionOn with | h a => rfl

/-- Exact naturality with the original postcomposition maps, in every degree. -/
theorem pathTransport_naturality (f : C(X, Y)) (γ : Path x₀ x₁) (n : ℕ)
    (a : HomotopyGroup.Pi n X x₀) :
    pathTransport (γ.map f.continuous) n (HomotopyGroup.map f rfl a) =
      HomotopyGroup.map f rfl (pathTransport γ n a) := by
  obtain ⟨b, rfl⟩ := (pathStartEquiv γ n).surjective a
  rw [← pathStartEquiv_postcomp]
  simpa only [pathStartEquiv_apply, pathEndEquiv_apply,
    pathTransport_homotopyGroupMap_start] using pathEndEquiv_postcomp f γ n b

/-- The map at the terminal point is the conjugate of the original map at the
initial point by the actual path transports. -/
theorem homotopyGroupMap_path_conjugate (f : C(X, Y)) (γ : Path x₀ x₁) (n : ℕ) :
    HomotopyGroup.map (N := Fin n) f (x := x₁) rfl =
      (pathTransport (γ.map f.continuous) n) ∘
        (HomotopyGroup.map f (x := x₀) rfl) ∘ (pathTransport γ n).symm := by
  funext a
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
    (pathTransport_naturality f γ n ((pathTransport γ n).symm a)).symm

/-- Injectivity of the actual map is invariant under a path in its source. -/
theorem homotopyGroupMap_injective_iff_of_path (f : C(X, Y))
    (γ : Path x₀ x₁) (n : ℕ) :
    Function.Injective (HomotopyGroup.map (N := Fin n) f (x := x₀) rfl) ↔
      Function.Injective (HomotopyGroup.map (N := Fin n) f (x := x₁) rfl) := by
  rw [homotopyGroupMap_path_conjugate f γ n, Equiv.comp_injective,
    Equiv.injective_comp]

/-- Surjectivity of the actual map is invariant under a path in its source. -/
theorem homotopyGroupMap_surjective_iff_of_path (f : C(X, Y))
    (γ : Path x₀ x₁) (n : ℕ) :
    Function.Surjective (HomotopyGroup.map (N := Fin n) f (x := x₀) rfl) ↔
      Function.Surjective (HomotopyGroup.map (N := Fin n) f (x := x₁) rfl) := by
  rw [homotopyGroupMap_path_conjugate f γ n, Equiv.comp_surjective,
    Equiv.surjective_comp]

/-- Bijectivity of the original all-degree map can be checked at either end
of any path.  In particular this applies in degree zero. -/
theorem homotopyGroupMap_bijective_iff_of_path (f : C(X, Y))
    (γ : Path x₀ x₁) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) f (x := x₀) rfl) ↔
      Function.Bijective (HomotopyGroup.map (N := Fin n) f (x := x₁) rfl) := by
  exact and_congr (homotopyGroupMap_injective_iff_of_path f γ n)
    (homotopyGroupMap_surjective_iff_of_path f γ n)

/-- The path-component form requires only actual existence of a path. -/
theorem homotopyGroupMap_bijective_iff_of_joined (f : C(X, Y))
    (h : Joined x₀ x₁) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) f (x := x₀) rfl) ↔
      Function.Bijective (HomotopyGroup.map (N := Fin n) f (x := x₁) rfl) :=
  homotopyGroupMap_bijective_iff_of_path f h.somePath n

/-- In a genuinely path-connected source it suffices to test the original map
at one specified point, separately in each finite degree. -/
theorem homotopyGroupMap_bijective_at_all_points [PathConnectedSpace X]
    (f : C(X, Y)) (x₀ : X) (n : ℕ)
    (h : Function.Bijective (HomotopyGroup.map (N := Fin n) f (x := x₀) rfl)) :
    ∀ x₁ : X, Function.Bijective (HomotopyGroup.map (N := Fin n) f (x := x₁) rfl) :=
  fun x₁ => (homotopyGroupMap_bijective_iff_of_path f (PathConnectedSpace.somePath x₀ x₁) n).mp h

/-- Transport takes the original constant class to the original constant class. -/
@[simp]
theorem pathTransport_const (γ : Path x₀ x₁) (n : ℕ) :
    pathTransport γ n (Quotient.mk' GenLoop.const) = Quotient.mk' GenLoop.const := by
  have hs : pathStartEquiv γ n (Quotient.mk' GenLoop.const) =
      Quotient.mk' GenLoop.const :=
    congrArg Quotient.mk' (GenLoop.postcomp_const (N := Fin n)
      (freePathEvaluation X 0) γ.source)
  have ht : pathEndEquiv γ n (Quotient.mk' GenLoop.const) =
      Quotient.mk' GenLoop.const :=
    congrArg Quotient.mk' (GenLoop.postcomp_const (N := Fin n)
      (freePathEvaluation X 1) γ.target)
  change HomotopyGroup.map (freePathEvaluation X 0) γ.source
    (Quotient.mk' GenLoop.const) = Quotient.mk' GenLoop.const at hs
  change HomotopyGroup.map (freePathEvaluation X 1) γ.target
    (Quotient.mk' GenLoop.const) = Quotient.mk' GenLoop.const at ht
  exact (congrArg (pathTransport γ n) hs.symm).trans
    ((pathTransport_homotopyGroupMap_start γ n _).trans ht)

/-- The constant path gives the identity on the original homotopy set. -/
@[simp]
theorem pathTransport_refl (x : X) (n : ℕ) :
    pathTransport (Path.refl x) n = Equiv.refl (HomotopyGroup.Pi n X x) := by
  apply Equiv.ext
  intro a
  have hs : pathStartEquiv (Path.refl x) n
      (HomotopyGroup.map ContinuousMap.const' rfl a) = a := by
    induction a using Quotient.inductionOn with | h a => rfl
  have ht : pathEndEquiv (Path.refl x) n
      (HomotopyGroup.map ContinuousMap.const' rfl a) = a := by
    induction a using Quotient.inductionOn with | h a => rfl
  change pathTransport (Path.refl x) n a = a
  change HomotopyGroup.map (freePathEvaluation X 0) (Path.refl x).source
    (HomotopyGroup.map ContinuousMap.const' rfl a) = a at hs
  change HomotopyGroup.map (freePathEvaluation X 1) (Path.refl x).target
    (HomotopyGroup.map ContinuousMap.const' rfl a) = a at ht
  exact (congrArg (pathTransport (Path.refl x) n) hs.symm).trans
    ((pathTransport_homotopyGroupMap_start _ _ _).trans ht)

end Topology
