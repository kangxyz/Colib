/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyPullback.Cartesian
public import Colib.Topology.Homotopy.HomotopyGroup.ProductWeakEquivalence
public import Colib.Topology.HomotopyPullback.WeakPasting

/-!
# Weak calculus for the original skeletal comparison squares

Coordinate transport, pasting and products retain the original constant-path
comparison. These are weak statements, without an ordinary homotopy inverse.


Implementation provenance:
`Quillen/Topology/Realization/Cartesian/WeakCalculus.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Topology.HomotopyPullback

/-- The identity square retains its canonical constant-path comparison.
From `Quillen/CategoryTheory/TheoremB/SkeletalCartesianCoordinates.lean` at the
same pinned source revision. -/
theorem cartesianIdentity {X A : Type u} [TopologicalSpace X] [TopologicalSpace A]
    (p : C(X, A)) : Cartesian p p (ContinuousMap.id X) (ContinuousMap.id A) rfl := by
  refine ⟨(HomotopyPullback.identityHomotopyEquiv p).trans
    (HomotopyPullback.symmetryHomeomorph (ContinuousMap.id A) p).toHomotopyEquiv, ?_⟩
  rfl

/-- A square whose two horizontal maps are prescribed homeomorphisms has
its genuine canonical homotopy equivalence, with arbitrary vertical maps. -/
theorem cartesianOfHorizontalHomeomorphs {W X A B : Type u}
    [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]
    (p : C(W, A)) (q : C(X, B)) (f : W ≃ₜ X) (g : A ≃ₜ B)
    (w : q.comp (f : C(W, X)) = (g : C(A, B)).comp p) :
    Cartesian p q (f : C(W,X)) (g : C(A,B)) w := by
  apply cartesianOfCoordinates _ _ _ _ _ q q (ContinuousMap.id X) (ContinuousMap.id B) rfl
    f (Homeomorph.refl X) g (Homeomorph.refl B)
  · exact w
  · rfl
  · rfl
  · rfl
  · exact cartesianIdentity q

/-- Complete weakness of the original canonical comparison. -/
abbrev WeakCartesian {W X A B : Type u} [TopologicalSpace W] [TopologicalSpace X]
    [TopologicalSpace A] [TopologicalSpace B]
    (p : C(W, A)) (q : C(X, B)) (f : C(W, X)) (g : C(A, B))
    (w : q.comp f = g.comp p) : Prop :=
  IsWeakHomotopyEquivalence (HomotopyPullback.comparison q g p f w)

/-- Existing genuine cartesian squares supply the weaker original-map property. -/
theorem Cartesian.weak {W X A B : Type u} [TopologicalSpace W] [TopologicalSpace X]
    [TopologicalSpace A] [TopologicalSpace B]
    {p : C(W, A)} {q : C(X, B)} {f : C(W, X)} {g : C(A, B)}
    {w : q.comp f = g.comp p} (h : Cartesian p q f g w) : WeakCartesian p q f g w := by
  change IsWeakHomotopyEquivalence (HomotopyPullback.comparison q g p f w)
  rw [← h.equiv_toFun]
  exact isWeakHomotopyEquivalence_of_homotopyEquiv h.equiv

/-- Strictly compatible original homeomorphisms transport complete weakness. -/
theorem weakCartesianOfCoordinates {W X A B W' X' A' B' : Type u}
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
    (h : WeakCartesian p' q' f' g' w') : WeakCartesian p q f g w := by
  let E := pullbackCoordinates q g q' g' eX eA eB wq wg
  have he : (HomotopyPullback.comparison q' g' p' f' w').comp eW.toHomotopyEquiv.toFun =
      E.toHomotopyEquiv.toFun.comp (HomotopyPullback.comparison q g p f w) := by
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    refine Prod.ext (ContinuousMap.congr_fun wp z) ?_
    refine Prod.ext (ContinuousMap.congr_fun wf z) ?_
    apply ContinuousMap.ext
    intro t
    exact (congrArg g' (ContinuousMap.congr_fun wp z)).trans
      (ContinuousMap.congr_fun wg (p z))
  have hw := h.comp (isWeakHomotopyEquivalence_of_homotopyEquiv eW.toHomotopyEquiv)
  rw [he] at hw
  exact hw.of_comp_right (isWeakHomotopyEquivalence_of_homotopyEquiv E.toHomotopyEquiv)

/-- Two weak-cartesian original squares paste with their full prescribed paths. -/
theorem WeakCartesian.paste {W X Y A B C : Type u}
    [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    {p : C(W, A)} {q : C(X, B)} {r : C(Y, C)}
    {f : C(W, X)} {f' : C(X, Y)} {g : C(A, B)} {g' : C(B, C)}
    {w : q.comp f = g.comp p} {w' : r.comp f' = g'.comp q}
    (h : WeakCartesian p q f g w) (h' : WeakCartesian q r f' g' w') :
    WeakCartesian p r (f'.comp f) (g'.comp g)
      (HomotopyPullback.pasteSquare p q r f f' g g' w w') :=
  HomotopyPullback.comparison_paste_isWeakHomotopyEquivalence p q r f f' g g' w w' h h'

/-- Equality transport changes no original map or stored path. -/
theorem WeakCartesian.congr {W X A B : Type u}
    [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]
    {p p' : C(W, A)} {q q' : C(X, B)} {f f' : C(W, X)} {g g' : C(A, B)}
    {w : q.comp f = g.comp p} {w' : q'.comp f' = g'.comp p'}
    (h : WeakCartesian p q f g w) (hp : p = p') (hq : q = q')
    (hf : f = f') (hg : g = g') : WeakCartesian p' q' f' g' w' := by
  subst p'
  subst q'
  subst f'
  subst g'
  exact h

/-- Products of original weak-cartesian squares are weak-cartesian, with
the two entire path coordinates paired literally. -/
theorem WeakCartesian.prod {W₁ W₂ X₁ X₂ A₁ A₂ B₁ B₂ : Type u}
    [TopologicalSpace W₁] [TopologicalSpace W₂] [TopologicalSpace X₁] [TopologicalSpace X₂]
    [TopologicalSpace A₁] [TopologicalSpace A₂] [TopologicalSpace B₁] [TopologicalSpace B₂]
    {p₁ : C(W₁, A₁)} {p₂ : C(W₂, A₂)} {q₁ : C(X₁, B₁)} {q₂ : C(X₂, B₂)}
    {f₁ : C(W₁, X₁)} {f₂ : C(W₂, X₂)} {g₁ : C(A₁, B₁)} {g₂ : C(A₂, B₂)}
    {w₁ : q₁.comp f₁ = g₁.comp p₁} {w₂ : q₂.comp f₂ = g₂.comp p₂}
    (h₁ : WeakCartesian p₁ q₁ f₁ g₁ w₁) (h₂ : WeakCartesian p₂ q₂ f₂ g₂ w₂) :
    WeakCartesian (p₁.prodMap p₂) (q₁.prodMap q₂) (f₁.prodMap f₂) (g₁.prodMap g₂)
      (ContinuousMap.ext fun x ↦ Prod.ext (ContinuousMap.congr_fun w₁ x.1)
        (ContinuousMap.congr_fun w₂ x.2)) :=
  (isWeakHomotopyEquivalence_of_homotopyEquiv
    (HomotopyPullback.prodHomeomorph q₁ q₂ g₁ g₂).toHomotopyEquiv).comp (h₁.prodMap h₂)

end Topology.HomotopyPullback
