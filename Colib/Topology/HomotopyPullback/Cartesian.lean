/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyPullback.Pasting
public import Colib.Topology.HomotopyPullback.Products

/-! # Canonical cartesian comparison calculus for actual skeletal charts -/
/-! Implementation source: `Quillen/Topology/Realization/Cartesian/Calculus.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The generic square calculus uses no
realization or cartesian pushout theorem. -/
@[expose] public section

noncomputable section
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Topology.HomotopyPullback

/-- A strict square is cartesian precisely when its actual constant-path
comparison is an ordinary homotopy equivalence. -/
def Cartesian {W X A B : Type u} [TopologicalSpace W] [TopologicalSpace X]
    [TopologicalSpace A] [TopologicalSpace B]
    (p : C(W, A)) (q : C(X, B)) (f : C(W, X)) (g : C(A, B))
    (w : q.comp f = g.comp p) : Prop :=
  ∃ e : ContinuousMap.HomotopyEquiv W (HomotopyPullback q g),
    e.toFun = HomotopyPullback.comparison q g p f w

/-- Select an equivalence without weakening the prescribed forward-map condition. -/
def Cartesian.equiv {W X A B : Type u} [TopologicalSpace W] [TopologicalSpace X]
    [TopologicalSpace A] [TopologicalSpace B]
    {p : C(W, A)} {q : C(X, B)} {f : C(W, X)} {g : C(A, B)}
    {w : q.comp f = g.comp p} (h : Cartesian p q f g w) :
    ContinuousMap.HomotopyEquiv W (HomotopyPullback q g) := h.choose

@[simp] theorem Cartesian.equiv_toFun {W X A B : Type u}
    [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]
    {p : C(W, A)} {q : C(X, B)} {f : C(W, X)} {g : C(A, B)}
    {w : q.comp f = g.comp p} (h : Cartesian p q f g w) :
    h.equiv.toFun = HomotopyPullback.comparison q g p f w := h.choose_spec

/-- Changing three spaces by genuine homeomorphisms transports the complete
path-space pullback, including its compact-open path topology. -/
def pullbackCoordinates {X A B X' A' B' : Type u}
    [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace X'] [TopologicalSpace A'] [TopologicalSpace B']
    (f : C(X, B)) (g : C(A, B)) (f' : C(X', B')) (g' : C(A', B'))
    (eX : X ≃ₜ X') (eA : A ≃ₜ A') (eB : B ≃ₜ B')
    (wf : f'.comp (eX : C(X, X')) = (eB : C(B, B')).comp f)
    (wg : g'.comp (eA : C(A, A')) = (eB : C(B, B')).comp g) :
    HomotopyPullback f g ≃ₜ HomotopyPullback f' g' where
  toFun z := ⟨(eA z.1.1, eX z.1.2.1, (eB : C(B,B')).comp z.1.2.2),
    (congrArg eB z.2.1).trans (ContinuousMap.congr_fun wf z.1.2.1).symm,
    (congrArg eB z.2.2).trans (ContinuousMap.congr_fun wg z.1.1).symm⟩
  invFun z := ⟨(eA.symm z.1.1, eX.symm z.1.2.1,
    (eB.symm : C(B',B)).comp z.1.2.2), by
      apply eB.injective
      simpa using z.2.1.trans (by
        simpa using ContinuousMap.congr_fun wf (eX.symm z.1.2.1)), by
      apply eB.injective
      simpa using z.2.2.trans (by
        simpa using ContinuousMap.congr_fun wg (eA.symm z.1.1))⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact eA.symm_apply_apply _
    · apply Prod.ext
      · exact eX.symm_apply_apply _
      · ext t
        exact eB.symm_apply_apply _
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact eA.apply_symm_apply _
    · apply Prod.ext
      · exact eX.apply_symm_apply _
      · ext t
        exact eB.apply_symm_apply _
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk (by fun_prop)
    apply Continuous.prodMk (by fun_prop)
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : HomotopyPullback f g × unitInterval ↦ eB (z.1.1.2.2 z.2))
    fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk (by fun_prop)
    apply Continuous.prodMk (by fun_prop)
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : HomotopyPullback f' g' × unitInterval ↦ eB.symm (z.1.1.2.2 z.2))
    fun_prop

/-- Cartesian comparisons are invariant under strictly compatible
homeomorphic coordinates on all four spaces. -/
theorem cartesianOfCoordinates {W X A B W' X' A' B' : Type u}
    [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace W'] [TopologicalSpace X'] [TopologicalSpace A'] [TopologicalSpace B']
    (p : C(W, A)) (q : C(X, B)) (f : C(W, X)) (g : C(A, B))
    (w : q.comp f = g.comp p)
    (p' : C(W', A')) (q' : C(X', B')) (f' : C(W', X')) (g' : C(A', B'))
    (w' : q'.comp f' = g'.comp p')
    (eW : W ≃ₜ W') (eX : X ≃ₜ X') (eA : A ≃ₜ A') (eB : B ≃ₜ B')
    (wp : p'.comp (eW : C(W, W')) = (eA : C(A, A')).comp p)
    (wq : q'.comp (eX : C(X, X')) = (eB : C(B, B')).comp q)
    (wf : f'.comp (eW : C(W, W')) = (eX : C(X, X')).comp f)
    (wg : g'.comp (eA : C(A, A')) = (eB : C(B, B')).comp g)
    (h : Cartesian p' q' f' g' w') : Cartesian p q f g w := by
  let E := pullbackCoordinates q g q' g' eX eA eB wq wg
  refine ⟨(eW.toHomotopyEquiv.trans h.equiv).trans E.symm.toHomotopyEquiv, ?_⟩
  ext z
  apply E.injective
  change E (E.symm (h.equiv (eW z))) = E (HomotopyPullback.comparison q g p f w z)
  rw [E.apply_symm_apply, h.equiv_toFun]
  apply Subtype.ext
  apply Prod.ext
  · exact ContinuousMap.congr_fun wp z
  · apply Prod.ext
    · exact ContinuousMap.congr_fun wf z
    · apply ContinuousMap.ext
      intro t
      change g' (p' (eW z)) = eB (g (p z))
      exact (congrArg g' (ContinuousMap.congr_fun wp z)).trans
        (ContinuousMap.congr_fun wg (p z))

/-- Two successive canonical cartesian squares paste. -/
theorem Cartesian.paste {W X Y A B C : Type u}
    [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    {p : C(W, A)} {q : C(X, B)} {r : C(Y, C)}
    {f : C(W, X)} {f' : C(X, Y)} {g : C(A, B)} {g' : C(B, C)}
    {w : q.comp f = g.comp p} {w' : r.comp f' = g'.comp q}
    (h : Cartesian p q f g w) (h' : Cartesian q r f' g' w') :
    Cartesian p r (f'.comp f) (g'.comp g)
      (HomotopyPullback.pasteSquare p q r f f' g g' w w') :=
  ⟨HomotopyPullback.pastingHomotopyEquiv p q r f f' g g' w w'
    h.equiv h.equiv_toFun h'.equiv h'.equiv_toFun, rfl⟩

/-- Every product square with an equivalence in its coefficient is canonical
homotopy cartesian, for an arbitrary parameter map. -/
theorem cartesianProduct {X Y A B : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace A] [TopologicalSpace B]
    (k : C(A, B)) (e : ContinuousMap.HomotopyEquiv X Y) :
    Cartesian (ContinuousMap.snd : C(X × A,A)) (ContinuousMap.snd : C(Y × B,B))
      (e.toFun.prodMap k) k rfl := by
  refine ⟨(Homeomorph.prodComm X A).toHomotopyEquiv.trans
    (HomotopyPullback.fiberProductHomotopyEquiv k e), ?_⟩
  rfl

/-- Equality of the four prescribed maps preserves canonical cartesianness. -/
theorem Cartesian.congr {W X A B : Type u}
    [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]
    {p p' : C(W, A)} {q q' : C(X, B)} {f f' : C(W, X)} {g g' : C(A, B)}
    {w : q.comp f = g.comp p} {w' : q'.comp f' = g'.comp p'}
    (h : Cartesian p q f g w) (hp : p = p') (hq : q = q')
    (hf : f = f') (hg : g = g') : Cartesian p' q' f' g' w' := by
  subst p'
  subst q'
  subst f'
  subst g'
  exact h

end Topology.HomotopyPullback
