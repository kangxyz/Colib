/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.Topology.Homotopy.Equiv

/-! Explicit homotopy equivalence data over a fixed parameter space. -/
/-! Implementation source: `Quillen/Topology/HomotopyEquiv/Fiberwise.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The prescribed continuous maps and
uniform parameter-preserving homotopies are retained. -/
@[expose] public section

noncomputable section
open scoped Topology unitInterval
open unitInterval
universe u
namespace Topology

/-- A homotopy is over a fixed base when every intermediate point has the
same specified projection as the source point. -/
def HomotopyOver {X Y A : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (p : X → A) (q : Y → A) {f g : C(X, Y)} (H : f.Homotopy g) : Prop :=
  ∀ t x, q (H (t, x)) = p x

namespace HomotopyOver
variable {X Y Z A : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {p : X → A} {q : Y → A} {r : Z → A}
  {f g h : C(X, Y)} {k l : C(Y, Z)}

theorem refl (f : C(X, Y)) (hf : ∀ x, q (f x) = p x) :
    HomotopyOver p q (ContinuousMap.Homotopy.refl f) := fun _ x ↦ hf x

theorem symm {H : f.Homotopy g} (hH : HomotopyOver p q H) : HomotopyOver p q H.symm :=
  fun t x ↦ hH (σ t) x

theorem trans {H : f.Homotopy g} {K : g.Homotopy h}
    (hH : HomotopyOver p q H) (hK : HomotopyOver p q K) : HomotopyOver p q (H.trans K) := by
  intro t x
  simp only [ContinuousMap.Homotopy.trans_apply]
  split_ifs <;> first | exact hH _ _ | exact hK _ _

theorem comp {H : f.Homotopy g} {K : k.Homotopy l}
    (hK : HomotopyOver q r K) (hH : HomotopyOver p q H) : HomotopyOver p r (K.comp H) :=
  fun t x ↦ (hK t (H (t, x))).trans (hH t x)

end HomotopyOver

/-- Standard explicit equivalence data, including actual inverse homotopies
that preserve the parameter. This is constructed below for concrete maps;
it is not an assumed localization or realization theorem. -/
structure FiberwiseHomotopyEquiv {X Y A : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace A] (p : C(X, A)) (q : C(Y, A)) where
  /-- The forward continuous map from `X` to `Y` over the common base `A`. -/
  toMap : C(X, Y)
  /-- The inverse continuous map from `Y` to `X` over the common base `A`. -/
  invMap : C(Y, X)
  /-- A specified homotopy from the inverse-after-forward composite to the identity on `X`. -/
  left : (invMap.comp toMap).Homotopy (ContinuousMap.id X)
  /-- A specified homotopy from the forward-after-inverse composite to the identity on `Y`. -/
  right : (toMap.comp invMap).Homotopy (ContinuousMap.id Y)
  /-- The forward map preserves the point in the base. -/
  to_over : ∀ x, q (toMap x) = p x
  /-- The inverse map preserves the point in the base. -/
  inv_over : ∀ y, p (invMap y) = q y
  /-- Every stage of the left inverse homotopy preserves the point in the base. -/
  left_over : HomotopyOver p p left
  /-- Every stage of the right inverse homotopy preserves the point in the base. -/
  right_over : HomotopyOver q q right

namespace FiberwiseHomotopyEquiv
variable {X Y Z W A : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z] [TopologicalSpace W] [TopologicalSpace A]
  {p : C(X, A)} {q : C(Y, A)} {r : C(Z, A)} {s : C(W, A)}

/-- Forget the maps' compatibility with the base and retain the underlying ordinary homotopy
equivalence between `X` and `Y`. -/
def toHomotopyEquiv (e : FiberwiseHomotopyEquiv p q) : ContinuousMap.HomotopyEquiv X Y :=
  ⟨e.toMap, e.invMap, ⟨e.left⟩, ⟨e.right⟩⟩

/-- Exchange the forward and inverse maps and their specified homotopies to obtain a fiberwise
homotopy equivalence from `q` to `p`. -/
def symm (e : FiberwiseHomotopyEquiv p q) : FiberwiseHomotopyEquiv q p :=
  ⟨e.invMap, e.toMap, e.right, e.left, e.inv_over, e.to_over, e.right_over, e.left_over⟩

/-- Compose the explicit maps and inverse homotopies over a common base. -/
def trans (e : FiberwiseHomotopyEquiv p q) (d : FiberwiseHomotopyEquiv q r) :
    FiberwiseHomotopyEquiv p r where
  toMap := d.toMap.comp e.toMap
  invMap := e.invMap.comp d.invMap
  left := (((ContinuousMap.Homotopy.refl e.invMap).comp d.left).comp
    (ContinuousMap.Homotopy.refl e.toMap)).trans e.left
  right := (((ContinuousMap.Homotopy.refl d.toMap).comp e.right).comp
    (ContinuousMap.Homotopy.refl d.invMap)).trans d.right
  to_over x := (d.to_over (e.toMap x)).trans (e.to_over x)
  inv_over z := (e.inv_over (d.invMap z)).trans (d.inv_over z)
  left_over := (((HomotopyOver.refl e.invMap e.inv_over).comp d.left_over).comp
    (HomotopyOver.refl e.toMap e.to_over)).trans e.left_over
  right_over := (((HomotopyOver.refl d.toMap d.to_over).comp e.right_over).comp
    (HomotopyOver.refl d.invMap d.inv_over)).trans d.right_over

/-- A homeomorphism over the base has constant inverse homotopies over it. -/
def ofHomeomorph (e : X ≃ₜ Y) (he : ∀ x, q (e x) = p x) : FiberwiseHomotopyEquiv p q where
  toMap := e
  invMap := e.symm
  left := { toFun := fun z ↦ z.2
            continuous_toFun := continuous_snd
            map_zero_left := fun x ↦ (e.symm_apply_apply x).symm
            map_one_left := fun _ ↦ rfl }
  right := { toFun := fun z ↦ z.2
             continuous_toFun := continuous_snd
             map_zero_left := fun y ↦ (e.apply_symm_apply y).symm
             map_one_left := fun _ ↦ rfl }
  to_over := he
  inv_over y := by simpa using (he (e.symm y)).symm
  left_over := fun _ _ ↦ rfl
  right_over := fun _ _ ↦ rfl

/-- Change the forward map along an actual homotopy over the base. -/
def replaceForward (e : FiberwiseHomotopyEquiv p q) (f : C(X, Y))
    (H : f.Homotopy e.toMap) (hH : HomotopyOver p q H) : FiberwiseHomotopyEquiv p q where
  toMap := f
  invMap := e.invMap
  left := ((ContinuousMap.Homotopy.refl e.invMap).comp H).trans e.left
  right := (H.comp (ContinuousMap.Homotopy.refl e.invMap)).trans e.right
  to_over x := (congrArg q (H.map_zero_left x)).symm.trans (hH 0 x)
  inv_over := e.inv_over
  left_over := ((HomotopyOver.refl e.invMap e.inv_over).comp hH).trans e.left_over
  right_over := (hH.comp (HomotopyOver.refl e.invMap e.inv_over)).trans e.right_over

/-- The two-out-of-six construction retains parameter-preserving actual
homotopies, instead of choosing unrelated homotopies fiber by fiber. -/
def ofAdjacentComposites
    (a : C(X, Y)) (b : C(Z, X)) (c : C(W, Z))
    (ha : ∀ x, q (a x) = p x) (hb : ∀ z, p (b z) = r z) (hc : ∀ w, r (c w) = s w)
    (e₁ : FiberwiseHomotopyEquiv r q) (e₂ : FiberwiseHomotopyEquiv s p)
    (h₁ : e₁.toMap = a.comp b) (h₂ : e₂.toMap = b.comp c) : FiberwiseHomotopyEquiv p q := by
  let H₁ : (e₁.invMap.comp (a.comp b)).Homotopy (ContinuousMap.id Z) := e₁.left.cast (by rw
    [h₁]) rfl
  let H₂ : ((b.comp c).comp e₂.invMap).Homotopy (ContinuousMap.id X) := e₂.right.cast (by rw
    [h₂]) rfl
  have hH₁ : HomotopyOver r r H₁ := e₁.left_over
  have hH₂ : HomotopyOver p p H₂ := e₂.right_over
  let R := ContinuousMap.Homotopy.refl ((b.comp e₁.invMap).comp a)
  let L := (R.comp H₂.symm).trans
    (((((ContinuousMap.Homotopy.refl b).comp H₁).comp
      (ContinuousMap.Homotopy.refl c)).comp
      (ContinuousMap.Homotopy.refl e₂.invMap)).trans H₂)
  refine {
    toMap := a
    invMap := b.comp e₁.invMap
    left := L
    right := e₁.right.cast (by rw [h₁]; rfl) rfl
    to_over := ha
    inv_over := fun y ↦ (hb (e₁.invMap y)).trans (e₁.inv_over y)
    left_over := ?_
    right_over := e₁.right_over }
  have hR : HomotopyOver p p R := HomotopyOver.refl _ (fun x ↦
    (hb (e₁.invMap (a x))).trans ((e₁.inv_over (a x)).trans (ha x)))
  exact (hR.comp hH₂.symm).trans
    (((((HomotopyOver.refl b hb).comp hH₁).comp
      (HomotopyOver.refl c hc)).comp
      (HomotopyOver.refl e₂.invMap e₂.inv_over)).trans hH₂)

end FiberwiseHomotopyEquiv
end Topology
