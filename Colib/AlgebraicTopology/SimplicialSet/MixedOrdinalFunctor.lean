/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.AlgebraicTopology.SimplicialSet.MixedOrdinalCylinder


/-! # Functoriality of the actual mixed cylinder -/
/-! Implementation provenance: extracted from
`Quillen/Topology/Realization/MixedOrdinalFunctor.lean`
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps, proofs,
assumptions, and universes are retained; only namespaces/imports are migrated.
-/
@[expose] public section

noncomputable section
open CategoryTheory Opposite
open scoped Simplicial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SSet.MixedOrdinalCylinder

/-- Act on mixed simplex data, leaving its cut unchanged. -/
def map {X Y : SSet.{u}} (f : X ⟶ Y) : cylinder X ⟶ cylinder Y where
  app n := ↾fun s ↦ ⟨s.1, f.app (op (mixedOrdinal s.1)) s.2⟩
  naturality n m α := by
    apply ConcreteCategory.hom_ext
    intro s
    change (⟨α.unop ≫ s.1, f.app _ (X.map _ s.2)⟩ : Simplex Y m.unop) =
      ⟨α.unop ≫ s.1, Y.map _ (f.app _ s.2)⟩
    congr 1
    exact ConcreteCategory.congr_hom (f.naturality _) s.2

/-- The mixed cylinder is a functor of simplicial sets. -/
def cylinderFunctor : SSet.{u} ⥤ SSet.{u} where
  obj := cylinder
  map := map
  map_id X := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    rfl
  map_comp f g := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    rfl

@[simp] theorem projection_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    map f ≫ projection Y = projection X ≫ f := by
  ext n s
  exact (ConcreteCategory.congr_hom (f.naturality (firstIndex s.1).op) s.2).symm

@[simp] theorem zeroSection_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    f ≫ zeroSection Y = zeroSection X ≫ map f := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  change (⟨zeroCut n.unop, Y.map _ (f.app _ x)⟩ : Simplex Y n.unop) =
    ⟨zeroCut n.unop, f.app _ (X.map _ x)⟩
  congr 1
  exact (ConcreteCategory.congr_hom (f.naturality (zeroCollapse n.unop).op) x).symm

@[simp] theorem oneSection_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    OrdinalSubdivision.subdivisionFunctor.map f ≫ oneSection Y = oneSection X ≫ map f := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro x
  change (⟨oneCut n.unop, Y.map _ (f.app _ x)⟩ : Simplex Y n.unop) =
    ⟨oneCut n.unop, f.app _ (X.map _ x)⟩
  congr 1
  exact (ConcreteCategory.congr_hom (f.naturality (inclusion (oneCut n.unop)).op) x).symm

/-- The natural projection from the mixed-cylinder functor to the identity functor. -/
def projectionNatTrans : cylinderFunctor.{u} ⟶ 𝟭 _ where
  app := projection
  naturality _ _ f := projection_naturality f

/-- The natural section of the mixed-cylinder functor at endpoint `0`, with source the identity
functor. -/
def zeroSectionNatTrans : 𝟭 _ ⟶ cylinderFunctor.{u} where
  app := zeroSection
  naturality _ _ f := zeroSection_naturality f

/-- The natural section of the mixed-cylinder functor at endpoint `1`, with source the
ordinary-subdivision functor. -/
def oneSectionNatTrans : OrdinalSubdivision.subdivisionFunctor.{u} ⟶ cylinderFunctor.{u} where
  app := oneSection
  naturality _ _ f := oneSection_naturality f

end SSet.MixedOrdinalCylinder
