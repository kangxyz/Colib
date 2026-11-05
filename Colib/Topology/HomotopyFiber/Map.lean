/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.Basic

/-! # Maps of actual homotopy fibers

A strictly commutative square induces a continuous map of the path-space
homotopy fibers. Identity and composition are proved pointwise.
-/
/-! Implementation source: `Quillen/Topology/HomotopyFiber/Map.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual path-space models,
basepoint tracks, maps and universe parameters are retained. -/
@[expose] public section

noncomputable section
universe u₁ u₂ u₃ v₁ v₂ v₃
open unitInterval

namespace Topology.HomotopyFiber
variable {X₁ : Type u₁} {X₂ : Type u₂} {X₃ : Type u₃}
  {Y₁ : Type v₁} {Y₂ : Type v₂} {Y₃ : Type v₃}
  [TopologicalSpace X₁] [TopologicalSpace X₂] [TopologicalSpace X₃]
  [TopologicalSpace Y₁] [TopologicalSpace Y₂] [TopologicalSpace Y₃]
  {f₁ : C(X₁, Y₁)} {f₂ : C(X₂, Y₂)} {f₃ : C(X₃, Y₃)}

/-- Functoriality of homotopy fibers under a commutative square. -/
def map (u : C(X₁, X₂)) (v : C(Y₁, Y₂)) (sq : v.comp f₁ = f₂.comp u)
    (y : Y₁) : C(HomotopyFiber f₁ y, HomotopyFiber f₂ (v y)) where
  toFun z := ⟨(u z.1.1, v.comp z.1.2),
    (congrArg v z.2.1).trans (ContinuousMap.congr_fun sq z.1.1), congrArg v z.2.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · exact (ContinuousMap.continuous_postcomp v).comp (by fun_prop)

/-- The source coordinate is the original square's total map. -/
@[simp] lemma map_source (u : C(X₁, X₂)) (v : C(Y₁, Y₂))
    (sq : v.comp f₁ = f₂.comp u) (y : Y₁) (z : HomotopyFiber f₁ y) :
    (map u v sq y z).1.1 = u z.1.1 := rfl

/-- The whole stored fiber path is postcomposed by the square's base map. -/
@[simp] lemma map_path (u : C(X₁, X₂)) (v : C(Y₁, Y₂))
    (sq : v.comp f₁ = f₂.comp u) (y : Y₁) (z : HomotopyFiber f₁ y) :
    (map u v sq y z).1.2 = v.comp z.1.2 := rfl

@[simp]
lemma projection_map (u : C(X₁, X₂)) (v : C(Y₁, Y₂))
    (sq : v.comp f₁ = f₂.comp u) (y : Y₁) :
    (projection f₂ (v y)).comp (map u v sq y) = u.comp (projection f₁ y) := by
  ext z
  rfl

@[simp]
lemma map_id (f : C(X₁, Y₁)) (y : Y₁) :
    map (f₁ := f) (f₂ := f) (ContinuousMap.id X₁) (ContinuousMap.id Y₁) rfl y =
      ContinuousMap.id (HomotopyFiber f y) := by
  ext z
  rfl

/-- Composition of fiber maps is the fiber map of the composed square. -/
@[simp] lemma map_comp_map (u : C(X₁, X₂)) (v : C(Y₁, Y₂)) (sq : v.comp f₁ = f₂.comp u)
    (u' : C(X₂, X₃)) (v' : C(Y₂, Y₃)) (sq' : v'.comp f₂ = f₃.comp u') (y : Y₁) :
    (map u' v' sq' (v y)).comp (map u v sq y) =
      map (u'.comp u) (v'.comp v)
        (show (v'.comp v).comp f₁ = f₃.comp (u'.comp u) by
          ext x
          exact (congrArg v' (ContinuousMap.congr_fun sq x)).trans
            (ContinuousMap.congr_fun sq' (u x))) y := by
  ext z
  rfl

/-- The induced fiber map preserves the distinguished constant-path points. -/
lemma map_basepoint (u : C(X₁, X₂)) (v : C(Y₁, Y₂))
    (sq : v.comp f₁ = f₂.comp u) (x : X₁) (y : Y₁) (h : f₁ x = y) :
    map u v sq y (basepoint f₁ y x h) =
      basepoint f₂ (v y) (u x)
        ((ContinuousMap.congr_fun sq x).symm.trans (congrArg v h)) := by
  apply Subtype.ext
  rfl

end Topology.HomotopyFiber
