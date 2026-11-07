/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.LESTail
public import Colib.Topology.HomotopyFiber.Map

/-!
# Naturality of the homotopy-fiber long exact sequence

A strictly commutative square of based continuous maps induces a map of the
actual path-space fibers. The projection, original-map, and connecting-map
squares commute on all homotopy sets. In positive degrees the connecting-square
identity is an equality of group homomorphisms.


Implementation provenance:
`Quillen/Topology/HomotopyFiber/LESNaturality.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section


noncomputable section
universe w u₁ u₂ v₁ v₂
namespace Topology.HomotopyFiber
variable {N : Type w} {X₁ : Type u₁} {X₂ : Type u₂} {Y₁ : Type v₁} {Y₂ : Type v₂}
  [TopologicalSpace X₁] [TopologicalSpace X₂] [TopologicalSpace Y₁] [TopologicalSpace Y₂]
  {f₁ : C(X₁, Y₁)} {f₂ : C(X₂, Y₂)}
  (u : C(X₁, X₂)) (v : C(Y₁, Y₂)) (sq : v.comp f₁ = f₂.comp u)
  (x : X₁) (y : Y₁) (h : f₁ x = y)

/-- A map of homotopy fibers commutes with the explicit loop inclusions. -/
theorem map_loopInclusion :
    (map u v sq y).comp (loopInclusion f₁ y x h) =
      (loopInclusion f₂ (v y) (u x)
        ((ContinuousMap.congr_fun sq x).symm.trans (congrArg v h))).comp (basedLoopMap v rfl) := by
  ext γ
  rfl

/-- Naturality of the homotopy-fiber projection on all homotopy sets. -/
theorem homotopyGroupMap_projection_natural
    (a : HomotopyGroup N (HomotopyFiber f₁ y) (basepoint f₁ y x h)) :
    HomotopyGroup.map u rfl
      (HomotopyGroup.map (projection f₁ y) (projection_basepoint f₁ y x h) a) =
    HomotopyGroup.map (projection f₂ (v y))
      (projection_basepoint f₂ (v y) (u x)
        ((ContinuousMap.congr_fun sq x).symm.trans (congrArg v h)))
      (HomotopyGroup.map (map u v sq y) (map_basepoint u v sq x y h) a) := by
  refine Quotient.inductionOn a (fun p => ?_)
  apply congrArg Quotient.mk'
  ext z
  rfl

/-- The given strictly commutative square induces a commutative square on
homotopy sets, including path components. -/
theorem homotopyGroupMap_square_natural (a : HomotopyGroup N X₁ x) :
    HomotopyGroup.map v rfl (HomotopyGroup.map f₁ h a) =
      HomotopyGroup.map f₂ ((ContinuousMap.congr_fun sq x).symm.trans (congrArg v h))
        (HomotopyGroup.map u rfl a) := by
  refine Quotient.inductionOn a (fun p => ?_)
  apply congrArg Quotient.mk'
  ext z
  exact ContinuousMap.congr_fun sq (p z)

/-- Naturality of the genuine connecting function in every degree, including
its pointed-set target in degree zero. -/
theorem connectingMap_natural (n : ℕ) (a : HomotopyGroup.Pi (n + 1) Y₁ y) :
    HomotopyGroup.map (map u v sq y) (map_basepoint u v sq x y h)
      (connectingMap f₁ y x h n a) =
    connectingMap f₂ (v y) (u x) ((ContinuousMap.congr_fun sq x).symm.trans (congrArg v h)) n
      (HomotopyGroup.map v rfl a) := by
  refine Quotient.inductionOn a (fun p => ?_)
  apply congrArg Quotient.mk'
  apply GenLoop.ext
  intro z
  apply Subtype.ext
  rfl

/-- Naturality of the connecting homomorphisms in the positive-degree LES. -/
theorem connectingHom_natural (n : ℕ) :
    (HomotopyGroup.piMap n (map u v sq y) (map_basepoint u v sq x y h)).comp
      (connectingHom f₁ y x h n) =
      (connectingHom f₂ (v y) (u x)
        ((ContinuousMap.congr_fun sq x).symm.trans (congrArg v h)) n).comp
          (HomotopyGroup.piMap (n + 1) v rfl) := by
  ext a
  exact connectingMap_natural u v sq x y h (n + 1) a

/-- Naturality of the projection homomorphisms in the positive-degree LES. -/
theorem projectionHom_natural (n : ℕ) :
    (HomotopyGroup.piMap n u rfl).comp
      (HomotopyGroup.piMap n (projection f₁ y) (projection_basepoint f₁ y x h)) =
      (HomotopyGroup.piMap n (projection f₂ (v y))
        (projection_basepoint f₂ (v y) (u x)
          ((ContinuousMap.congr_fun sq x).symm.trans (congrArg v h)))).comp
        (HomotopyGroup.piMap n (map u v sq y) (map_basepoint u v sq x y h)) := by
  ext a
  exact homotopyGroupMap_projection_natural u v sq x y h a

/-- Naturality of the original-map homomorphisms in the positive-degree LES. -/
theorem originalHom_natural (n : ℕ) :
    (HomotopyGroup.piMap n v rfl).comp (HomotopyGroup.piMap n f₁ h) =
      (HomotopyGroup.piMap n f₂ ((ContinuousMap.congr_fun sq x).symm.trans (congrArg v h))).comp
        (HomotopyGroup.piMap n u rfl) := by
  ext a
  exact homotopyGroupMap_square_natural u v sq x y h a

end Topology.HomotopyFiber
