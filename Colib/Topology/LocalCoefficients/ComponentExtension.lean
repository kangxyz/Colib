/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.Abelian
public import Colib.Topology.FundamentalGroupoid.PathComponent

/-!
Adapted from `Quillen/Topology/LocalCoefficients/ComponentExtension.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using native Colib objects.

# Extending actual local coefficients by zero from a path component

The component inclusion is fully faithful on fundamental groupoids. The
extension uses its unique path-class preimages on the component and the zero
module elsewhere. Saturation under paths supplies the genuine functor laws.
The canonical restriction isomorphism preserves all original path transport;
no openness of the component is assumed.
-/

@[expose] public section
noncomputable section
open Topology CategoryTheory Limits
open scoped ZeroObject
universe u v
namespace FundamentalGroupoid.LocalCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {Y : Type u} [TopologicalSpace Y] (y : Y)
  (A : System.{u, v} (pathComponent y))

/-- The original component fiber, or the actual zero module off the component. -/
def componentExtensionObj (a : FundamentalGroupoid Y) : ModuleCat.{v} ℤ := by
  classical
  exact if ha : a.as ∈ pathComponent y then
    A.obj (FundamentalGroupoid.mk (⟨a.as, ha⟩ : pathComponent y)) else 0

/-- The canonical fiber identification at a point of the component. -/
def componentExtensionObjIso (a : FundamentalGroupoid Y) (ha : a.as ∈ pathComponent y) :
    componentExtensionObj y A a ≅
      A.obj (FundamentalGroupoid.mk (⟨a.as, ha⟩ : pathComponent y)) := by
  classical
  exact eqToIso (dite_eq_left ha)

/-- Extension transport uses the unique original restricted path class. -/
def componentExtensionMap {a b : FundamentalGroupoid Y} (f : a ⟶ b) :
    componentExtensionObj y A a ⟶ componentExtensionObj y A b := by
  classical
  exact if ha : a.as ∈ pathComponent y then
    let hb := FundamentalGroupoid.Component.mem_of_hom y f ha
    (componentExtensionObjIso y A a ha).hom ≫
      A.map ((FundamentalGroupoid.Component.inclusionMap y).preimage
        (X := FundamentalGroupoid.mk (⟨a.as, ha⟩ : pathComponent y))
        (Y := FundamentalGroupoid.mk (⟨b.as, hb⟩ : pathComponent y)) f) ≫
      (componentExtensionObjIso y A b hb).inv
  else 0

/-- The inside-component transport formula retains the canonical fiber identifications. -/
lemma componentExtensionMap_of_mem {a b : FundamentalGroupoid Y} (f : a ⟶ b)
    (ha : a.as ∈ pathComponent y) (hb : b.as ∈ pathComponent y) :
    componentExtensionMap y A f =
      (componentExtensionObjIso y A a ha).hom ≫
        A.map ((FundamentalGroupoid.Component.inclusionMap y).preimage
          (X := FundamentalGroupoid.mk (⟨a.as, ha⟩ : pathComponent y))
          (Y := FundamentalGroupoid.mk (⟨b.as, hb⟩ : pathComponent y)) f) ≫
        (componentExtensionObjIso y A b hb).inv := by
  classical
  simp only [componentExtensionMap, dite_eq_left ha]

/-- Every arrow with source off the component is sent to the zero morphism. -/
lemma componentExtensionMap_of_not_mem {a b : FundamentalGroupoid Y} (f : a ⟶ b)
    (ha : a.as ∉ pathComponent y) : componentExtensionMap y A f = 0 := by
  classical
  simp only [componentExtensionMap, dite_eq_right ha]

/-- The genuine local system extending the original system by zero. -/
def componentExtension : System.{u, v} Y where
  obj := componentExtensionObj y A
  map := componentExtensionMap y A
  map_id a := by
    classical
    by_cases ha : a.as ∈ pathComponent y
    · rw [componentExtensionMap_of_mem y A (𝟙 a) ha ha]
      erw [Functor.preimage_id, A.map_id, Category.id_comp, Iso.hom_inv_id]
    · rw [componentExtensionMap_of_not_mem y A (𝟙 a) ha]
      have hz : componentExtensionObj y A a = 0 := by
        simp only [componentExtensionObj, dite_eq_right ha]
      rw [hz]
      exact (isZero_zero (ModuleCat.{v} ℤ)).eq_of_src _ _
  map_comp {a b c} f g := by
    classical
    by_cases ha : a.as ∈ pathComponent y
    · have hb := FundamentalGroupoid.Component.mem_of_hom y f ha
      have hc := FundamentalGroupoid.Component.mem_of_hom y g hb
      rw [componentExtensionMap_of_mem y A f ha hb,
        componentExtensionMap_of_mem y A g hb hc,
        componentExtensionMap_of_mem y A (f ≫ g) ha hc]
      erw [Functor.preimage_comp (F := FundamentalGroupoid.Component.inclusionMap y)
        (X := FundamentalGroupoid.mk (⟨a.as, ha⟩ : pathComponent y))
        (Y := FundamentalGroupoid.mk (⟨b.as, hb⟩ : pathComponent y))
        (Z := FundamentalGroupoid.mk (⟨c.as, hc⟩ : pathComponent y)) f g,
        Functor.map_comp]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    · rw [componentExtensionMap_of_not_mem y A f ha,
        componentExtensionMap_of_not_mem y A (f ≫ g) ha, zero_comp]


/-- Extension by zero preserves the original abelian-monodromy condition. -/
theorem componentExtension_abelianMonodromy (hA : AbelianMonodromy A) :
    AbelianMonodromy (componentExtension y A) := by
  classical
  intro a f g
  change componentExtensionMap y A f ≫ componentExtensionMap y A g =
    componentExtensionMap y A g ≫ componentExtensionMap y A f
  by_cases ha : a.as ∈ pathComponent y
  · rw [componentExtensionMap_of_mem y A f ha ha,
      componentExtensionMap_of_mem y A g ha ha]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
      congrArg (fun k => (componentExtensionObjIso y A a ha).hom ≫ k ≫
        (componentExtensionObjIso y A a ha).inv)
        (hA (FundamentalGroupoid.mk (⟨a.as, ha⟩ : pathComponent y))
          ((FundamentalGroupoid.Component.inclusionMap y).preimage f)
          ((FundamentalGroupoid.Component.inclusionMap y).preimage g))
  · rw [componentExtensionMap_of_not_mem y A f ha,
      componentExtensionMap_of_not_mem y A g ha]

/-- Outside the original component, the coefficient fiber is literally the zero module. -/
lemma componentExtension_fiber_off (x : Y) (hx : x ∉ pathComponent y) :
    fiber (componentExtension y A) x = 0 := by
  classical
  simp only [fiber, componentExtension, componentExtensionObj, dite_eq_right hx]

/-- The extension is supported on the original path component. -/
lemma componentExtension_isZero_off (x : Y) (hx : x ∉ pathComponent y) :
    IsZero (fiber (componentExtension y A) x) := by
  rw [componentExtension_fiber_off y A x hx]
  exact isZero_zero _

/-- Pullback along the original inclusion recovers the original coefficient system canonically. -/
def componentExtensionPullbackIso :
    pullback (FundamentalGroupoid.Component.inclusion y) (componentExtension y A) ≅ A :=
  NatIso.ofComponents (fun a =>
    componentExtensionObjIso y A
      ((FundamentalGroupoid.Component.inclusionMap y).obj a) a.as.property) (by
    intro a b f
    change componentExtensionMap y A ((FundamentalGroupoid.Component.inclusionMap y).map f) ≫
        (componentExtensionObjIso y A
          ((FundamentalGroupoid.Component.inclusionMap y).obj b) b.as.property).hom =
      (componentExtensionObjIso y A
        ((FundamentalGroupoid.Component.inclusionMap y).obj a) a.as.property).hom ≫ A.map f
    rw [componentExtensionMap_of_mem y A _ a.as.property b.as.property,
      Functor.preimage_map]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- Every actual ambient path in the component retains the original restricted transport. -/
lemma componentExtension_transport {a b : pathComponent y} (p : Path a.val b.val) :
    transport (componentExtension y A) p ≫
        (componentExtensionPullbackIso y A).hom.app (FundamentalGroupoid.mk b) =
      (componentExtensionPullbackIso y A).hom.app (FundamentalGroupoid.mk a) ≫
        transport A (pathComponentPath p) := by
  have h := (componentExtensionPullbackIso y A).hom.naturality
    (Path.Homotopic.Quotient.mk (pathComponentPath p))
  change transport (pullback (FundamentalGroupoid.Component.inclusion y)
    (componentExtension y A)) (pathComponentPath p) ≫ _ = _ at h
  rw [pullback_transport] at h
  change transport (componentExtension y A)
      ((pathComponentPath p).map continuous_subtype_val) ≫ _ =
    _ ≫ transport A (pathComponentPath p) at h
  rw [pathComponentPath_map] at h
  exact h

end FundamentalGroupoid.LocalCoefficients
