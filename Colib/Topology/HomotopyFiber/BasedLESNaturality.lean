/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.LESNaturality
public import Colib.Topology.HomotopyFiber.BasedSquareMap

/-!
# Original connecting naturality at specified target basepoints

Both given basepoint equalities are retained by the actual fiber map.
The full original connecting homomorphisms commute.
-/
/-! Implementation source: `Quillen/Topology/HomotopyFiber/BasedLESNaturality.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Both specified basepoint equalities
and the actual projection and connecting homomorphisms are retained. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology
universe u v w z
namespace Topology.HomotopyFiber
section Based
variable {X : Type u} {Y : Type v} {A : Type w} {B : Type z}
    [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace A] [TopologicalSpace B] {f : C(X, A)} {g : C(Y, B)}
    (p : C(X, Y)) (q : C(A, B)) (sq : q.comp f = g.comp p)
    (x : X) (a : A) (y : Y) (b : B) (h : f x = a) (h' : g y = b)
    (hx : p x = y) (ha : q a = b)

include hx in
/-- The original fiber map preserves both specified basepoint equalities. -/
lemma mapAt_basepoint :
    mapAt p q sq a b ha (basepoint f a x h) = basepoint g b y h' := by
  apply Subtype.ext
  apply Prod.ext hx
  exact ContinuousMap.ext (fun _ => ha)

/-- The original connecting homomorphism commutes with the endpoint-aware fiber map. -/
lemma connectingHom_mapAt_natural (n : ℕ) :
    (HomotopyGroup.piMap n (mapAt p q sq a b ha) (mapAt_basepoint p q sq x a y b h h' hx ha)).comp
      (connectingHom f a x h n) =
    (connectingHom g b y h' n).comp (HomotopyGroup.piMap (n+1) q ha) := by
  subst y
  subst b
  exact connectingHom_natural p q sq x a h n

/-- The original projection homomorphism commutes with the endpoint-aware fiber map. -/
theorem projectionHom_mapAt_natural (n : ℕ) :
    (HomotopyGroup.piMap n (projection g b) (projection_basepoint g b y h')).comp
      (HomotopyGroup.piMap n (mapAt p q sq a b ha)
        (mapAt_basepoint p q sq x a y b h h' hx ha)) =
    (HomotopyGroup.piMap n p hx).comp
      (HomotopyGroup.piMap n (projection f a) (projection_basepoint f a x h)) := by
  subst y
  subst b
  exact (projectionHom_natural p q sq x a h n).symm

end Based
end Topology.HomotopyFiber
