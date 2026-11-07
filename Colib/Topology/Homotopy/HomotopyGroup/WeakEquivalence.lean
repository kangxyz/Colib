/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Homotopy.HomotopyGroup.Equivalence

/-! Canonical all-degree homotopy-set bijectivity, including π₀, with
composition and actual fixed-basepoint homotopy transport. -/
/-! Implementation source: `Quillen/Topology/HomotopyGroups/WeakEquivalence.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`; the actual maps and hypotheses are retained. -/
@[expose] public section

noncomputable section
universe u v w
namespace Topology
variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {x : X} {y : Y} {z : Z}

/-- An ordinary, potentially unbased homotopy equivalence gives the canonical
bijection even on π₀. No based inverse is supplied or assumed. -/
theorem homotopyGroupMap_bijective_of_homotopyEquiv
    (e : ContinuousMap.HomotopyEquiv X Y) (h : e.toFun x = y) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) e.toFun h) := by
  cases n with
  | succ n => exact piMap_bijective_of_homotopyEquiv e h n
  | zero =>
    constructor
    · intro a b hab
      induction a using Quotient.inductionOn with | h a =>
        induction b using Quotient.inductionOn with | h b =>
          obtain ⟨H⟩ := Quotient.exact hab
          have Ha := e.left_inv.comp (ContinuousMap.Homotopic.refl a.val)
          have Hb := e.left_inv.comp (ContinuousMap.Homotopic.refl b.val)
          have H' : (e.toFun.comp a.val).Homotopic (e.toFun.comp b.val) := ⟨H.toHomotopy⟩
          obtain ⟨K⟩ := Ha.symm.trans
            (((ContinuousMap.Homotopic.refl e.invFun).comp H').trans Hb)
          exact Quotient.sound ⟨{
            toHomotopy := K
            prop' := by rintro t s ⟨i, _⟩; exact Fin.elim0 i }⟩
    · intro a
      induction a using Quotient.inductionOn with | h p =>
        let q : GenLoop (Fin 0) X x :=
          ⟨e.invFun.comp p.val, by rintro s ⟨i, _⟩; exact Fin.elim0 i⟩
        obtain ⟨H⟩ := e.right_inv.comp (ContinuousMap.Homotopic.refl p.val)
        refine ⟨Quotient.mk' q, Quotient.sound ⟨?_⟩⟩
        exact {
          toHomotopy := H
          prop' := by rintro t s ⟨i, _⟩; exact Fin.elim0 i }

/-- Composition preserves bijectivity of the actual based maps in every degree. -/
theorem homotopyGroupMap_bijective_comp (f : C(X, Y)) (g : C(Y, Z))
    (hf : f x = y) (hg : g y = z) (n : ℕ)
    (hfb : Function.Bijective (HomotopyGroup.map (N := Fin n) f hf))
    (hgb : Function.Bijective (HomotopyGroup.map (N := Fin n) g hg)) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) (g.comp f)
      ((congrArg g hf).trans hg)) := by
  have he : HomotopyGroup.map (N := Fin n) (g.comp f) ((congrArg g hf).trans hg) =
      (HomotopyGroup.map (N := Fin n) g hg) ∘ (HomotopyGroup.map (N := Fin n) f hf) := by
    funext a
    exact HomotopyGroup.map_comp f hf g hg a
  rw [he]
  exact hgb.comp hfb

/-- A supplied homotopy fixed at the stated source point retains bijectivity;
the fixed-point condition is explicit and must be proved at the application. -/
theorem homotopyGroupMap_bijective_of_based_homotopy {f g : C(X, Y)}
    (hf : f x = y) (hg : g x = y) (H : f.Homotopy g)
    (hH : ∀ t, H (t, x) = y) (n : ℕ)
    (hb : Function.Bijective (HomotopyGroup.map (N := Fin n) f hf)) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) g hg) := by
  rw [← HomotopyGroup.map_eq_of_based_homotopy hf hg H hH]
  exact hb

/-- Equality of continuous maps identifies the induced maps even when their
endpoint equalities have different proof terms. -/
theorem homotopyGroupMap_congr {N : Type*} {f g : C(X, Y)} (hfg : f = g)
    (hf : f x = y) (hg : g x = y) :
    HomotopyGroup.map (N := N) f hf = HomotopyGroup.map (N := N) g hg := by
  cases hfg
  rfl

theorem homotopyGroupMap_bijective_congr {N : Type*} {f g : C(X, Y)} (hfg : f = g)
    (hf : f x = y) (hg : g x = y)
    (hb : Function.Bijective (HomotopyGroup.map (N := N) f hf)) :
    Function.Bijective (HomotopyGroup.map (N := N) g hg) := by
  rw [← homotopyGroupMap_congr hfg hf hg]
  exact hb

end Topology
