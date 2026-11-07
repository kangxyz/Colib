/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.Homotopy.Basic

/-! Actual reduced mapping-cone quotient and its continuous original maps.
No homotopy invariance or stable cofiber assertion is part of the definition. -/
/-! Implementation provenance: adapted from
`Quillen/Topology/HomotopyCofiber/ReducedMappingCone.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The literal quotient relation,
original target and cylinder maps, independent universes, and complete chosen
nullhomotopy are retained. Only native namespace ownership changes. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
open unitInterval
universe u v w u' v'
namespace Topology.ReducedMappingCone
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (x₀ : X) (y₀ : Y) (f : C(X, Y))

/-- Glue the cylinder bottom along the map and collapse its top and basepoint line. -/
inductive Relation : Y ⊕ (I × X) → Y ⊕ (I × X) → Prop
  | bottom (x : X) : Relation (.inr (0,x)) (.inl (f x))
  | top (x : X) : Relation (.inr (1,x)) (.inl y₀)
  | base (t : I) : Relation (.inr (t,x₀)) (.inl y₀)

/-- The quotient topological space of the reduced mapping cone. -/
abbrev Space := Quot (Relation x₀ y₀ f)

/-- The inclusion of the target into the reduced mapping cone. -/
def inr : C(Y, Space x₀ y₀ f) :=
  ⟨fun y ↦ Quot.mk _ (.inl y), continuous_quot_mk.comp continuous_inl⟩

/-- The original cylinder map into the reduced mapping cone. -/
def cylinder : C(I × X, Space x₀ y₀ f) :=
  ⟨fun z ↦ Quot.mk _ (.inr z), continuous_quot_mk.comp continuous_inr⟩

/-- The image of the target basepoint in the reduced mapping cone. -/
def point : Space x₀ y₀ f := inr x₀ y₀ f y₀

@[simp] theorem cylinder_zero (x : X) : cylinder x₀ y₀ f (0,x) = inr x₀ y₀ f (f x) :=
  Quot.sound (Relation.bottom x)
@[simp] theorem cylinder_one (x : X) : cylinder x₀ y₀ f (1,x) = point x₀ y₀ f :=
  Quot.sound (Relation.top x)
@[simp] theorem cylinder_base (t : I) : cylinder x₀ y₀ f (t,x₀) = point x₀ y₀ f :=
  Quot.sound (Relation.base t)

/-- The literal cone coordinate contracts the original composite, relative to its base point. -/
def nullHomotopy (hf : f x₀ = y₀) :
    ((inr x₀ y₀ f).comp f).HomotopyRel (ContinuousMap.const X (point x₀ y₀ f)) {x₀} where
  toFun := cylinder x₀ y₀ f
  continuous_toFun := (cylinder x₀ y₀ f).continuous
  map_zero_left := cylinder_zero x₀ y₀ f
  map_one_left := cylinder_one x₀ y₀ f
  prop' t x hx := by
    have hx : x = x₀ := hx
    subst x
    simpa only [point, ContinuousMap.coe_mk, ContinuousMap.comp_apply, hf] using cylinder_base
      x₀ y₀ f t

variable {Z : Type w} [TopologicalSpace Z]

/-- Descend an actual map together with a chosen based nullhomotopy. -/
def desc (g : C(Y, Z)) (H : C(I × X, Z))
    (h₀ : ∀ x, H (0, x) = g (f x))
    (h₁ : ∀ x, H (1, x) = g y₀)
    (hb : ∀ t, H (t, x₀) = g y₀) : C(Space x₀ y₀ f,Z) where
  toFun := Quot.lift (Sum.elim g H) (by
    intro a b h
    cases h with
    | bottom x => exact h₀ x
    | top x => exact h₁ x
    | base t => exact hb t)
  continuous_toFun := continuous_quot_lift _ (g.continuous.sumElim H.continuous)

@[simp] theorem desc_inr (g : C(Y, Z)) (H : C(I × X, Z)) h₀ h₁ hb (y : Y) :
    desc x₀ y₀ f g H h₀ h₁ hb (inr x₀ y₀ f y) = g y := rfl
@[simp] theorem desc_cylinder (g : C(Y, Z)) (H : C(I × X, Z)) h₀ h₁ hb (z : I × X) :
    desc x₀ y₀ f g H h₀ h₁ hb (cylinder x₀ y₀ f z) = H z := rfl

@[ext] theorem hom_ext {g h : C(Space x₀ y₀ f, Z)}
    (hi : ∀ y, g (inr x₀ y₀ f y) = h (inr x₀ y₀ f y))
    (hc : ∀ z, g (cylinder x₀ y₀ f z) = h (cylinder x₀ y₀ f z)) : g = h := by
  ext q
  induction q using Quot.inductionOn with
  | h z => cases z with
    | inl y => exact hi y
    | inr z => exact hc z

variable {X' : Type u'} {Y' : Type v'} [TopologicalSpace X'] [TopologicalSpace Y']
  (x₀' : X') (y₀' : Y') (f' : C(X', Y'))

/-- The actual mapping-cone map of a strictly commuting based square. -/
def map (a : C(X, X')) (b : C(Y, Y')) (ha : a x₀ = x₀') (hb : b y₀ = y₀')
    (comm : ∀ x, b (f x) = f' (a x)) :
    C(Space x₀ y₀ f, Space x₀' y₀' f') :=
  desc x₀ y₀ f ((inr x₀' y₀' f').comp b)
    ⟨fun z ↦ cylinder x₀' y₀' f' (z.1,a z.2), by fun_prop⟩
    (fun x ↦ (cylinder_zero x₀' y₀' f' (a x)).trans (congrArg (inr x₀' y₀' f') (comm x).symm))
    (fun x ↦ (cylinder_one x₀' y₀' f' (a x)).trans (congrArg (inr x₀' y₀' f') hb.symm))
    (fun t ↦ by
      change cylinder x₀' y₀' f' (t,a x₀) = inr x₀' y₀' f' (b y₀)
      simpa only [point, ha, hb] using cylinder_base x₀' y₀' f' t)

@[simp] theorem map_inr (a : C(X, X')) (b : C(Y, Y')) ha hb comm (y : Y) :
    map x₀ y₀ f x₀' y₀' f' a b ha hb comm (inr x₀ y₀ f y) = inr x₀' y₀' f' (b y) := rfl
@[simp] theorem map_cylinder (a : C(X, X')) (b : C(Y, Y')) ha hb comm (z : I × X) :
    map x₀ y₀ f x₀' y₀' f' a b ha hb comm (cylinder x₀ y₀ f z) = cylinder x₀' y₀' f' (z.1,a z.2)
      := rfl
@[simp] theorem map_point (a : C(X, X')) (b : C(Y, Y')) ha hb comm :
    map x₀ y₀ f x₀' y₀' f' a b ha hb comm (point x₀ y₀ f) = point x₀' y₀' f' :=
  congrArg (inr x₀' y₀' f') hb

end Topology.ReducedMappingCone
