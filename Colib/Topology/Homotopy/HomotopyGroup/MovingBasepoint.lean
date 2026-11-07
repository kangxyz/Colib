/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.PathTransport

/-!
# Homotopy classes with a displayed moving basepoint

An actual cube homotopy whose entire boundary follows one displayed path identifies the
original endpoint classes by the existing free-path-space transport, in every finite degree.
The same formula applies to an unbased homotopy of continuous maps and retains its actual
basepoint track. No path-connectedness or choice of a path between components is assumed.
-/

/-! Implementation source: `Quillen/Topology/HomotopyGroups/MovingBasepoint.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual maps, endpoint paths,
universes and signs are retained, with native Colib dependencies. -/
/-! The endpoint-cast lemma is extracted from
`Quillen/Topology/ClassifyingSpace/NaturalTransformationTracks.lean` at the same revision,
and belongs here because it applies to arbitrary continuous maps. -/
@[expose] public section

noncomputable section

open scoped Topology unitInterval

universe u v

namespace Topology

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- A cube homotopy with the displayed moving boundary realizes the original path transport. -/
theorem pathTransport_eq_of_cube_homotopy {x y : X} (γ : Path x y) (n : ℕ)
    (p : GenLoop (Fin n) X x) (q : GenLoop (Fin n) X y)
    (H : p.val.Homotopy q.val)
    (hH : ∀ t s, s ∈ Cube.boundary (Fin n) → H (t, s) = γ t) :
    pathTransport γ n (Quotient.mk' p) = Quotient.mk' q := by
  let L : GenLoop (Fin n) C(unitInterval, X) γ.toContinuousMap :=
    ⟨{ toFun s := ⟨fun t ↦ H (t, s), by fun_prop⟩
       continuous_toFun := by
         apply ContinuousMap.continuous_of_continuous_uncurry
         exact H.continuous.comp continuous_swap }, by
      intro s hs
      ext t
      exact hH t s hs⟩
  have h₀ : HomotopyGroup.map (freePathEvaluation X 0) γ.source (Quotient.mk' L) =
      Quotient.mk' p := by
    apply congrArg Quotient.mk'
    apply Subtype.ext
    ext s
    exact H.apply_zero s
  have h₁ : HomotopyGroup.map (freePathEvaluation X 1) γ.target (Quotient.mk' L) =
      Quotient.mk' q := by
    apply congrArg Quotient.mk'
    apply Subtype.ext
    ext s
    exact H.apply_one s
  exact (congrArg (pathTransport γ n) h₀.symm).trans
    ((pathTransport_homotopyGroupMap_start γ n _).trans h₁)

/-- An unbased homotopy identifies its original induced maps by transport along the exact
track of the displayed source point, including degree zero. -/
theorem pathTransport_homotopyGroupMap_homotopy {f g : C(X, Y)}
    (H : f.Homotopy g) (x : X) (n : ℕ) (a : HomotopyGroup.Pi n X x) :
    pathTransport (H.evalAt x) n (HomotopyGroup.map f rfl a) =
      HomotopyGroup.map g rfl a := by
  induction a using Quotient.inductionOn with
  | h p =>
    apply pathTransport_eq_of_cube_homotopy (H.evalAt x) n
      (GenLoop.postcomp f rfl p) (GenLoop.postcomp g rfl p)
      (H.comp (ContinuousMap.Homotopy.refl p.val))
    intro t s hs
    change H (t, p s) = H (t, x)
    exact congrArg (fun z ↦ H (t, z)) (p.property s hs)

/-- An unbased homotopy with identified endpoints still requires its whole track. -/
theorem pathTransport_homotopyGroupMap_homotopy_cast
    {f g : C(X, Y)} (H : f.Homotopy g) (x : X) {y₀ y₁ : Y}
    (hf : f x = y₀) (hg : g x = y₁) (n : ℕ) (a : HomotopyGroup.Pi n X x) :
    pathTransport ((H.evalAt x).cast hf.symm hg.symm) n (HomotopyGroup.map f hf a) =
      HomotopyGroup.map g hg a := by
  subst y₀ y₁
  exact pathTransport_homotopyGroupMap_homotopy H x n a

end Topology
