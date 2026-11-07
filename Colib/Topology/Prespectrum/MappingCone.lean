/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyCofiber.ReducedMappingCone
public import Colib.Topology.Prespectrum.Homotopy
public import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Actual reduced mapping cones of loop prespectra

The quotient cone is constructed levelwise. The original structure square descends to a
continuous map into loops on the next cone, retaining the independent cylinder and loop
parameters. This gives a functor on strict arrow squares, a coherent based nullhomotopy,
and unique descent from specified actual maps and nullhomotopies. This owner asserts
neither the Omega property nor stable cofiber exactness.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/MappingCone.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The actual cone, full independent cylinder and loop parameters, signed degrees and
original hypotheses are retained under their native mathematical owners. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
open unitInterval
universe u v u' v'
namespace Topology.ReducedMappingCone
variable {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
  (x₀ : X) (y₀ : Y) (f : C(X, Y)) (x₀' : X') (y₀' : Y') (f' : C(X', Y'))
  (hf' : f' x₀' = y₀')
  (a : C(X, Path x₀' x₀')) (b : C(Y, Path y₀' y₀'))
  (ha : a x₀ = Path.refl x₀') (hb : b y₀ = Path.refl y₀')
  (comm : ∀ x, basedLoopMap f' hf' (a x) = b (f x))

/-- The original cone coordinate remains independent of the actual loop parameter. -/
def cylinderLoop : C(I × X, Path (point x₀' y₀' f') (point x₀' y₀' f')) where
  toFun z :=
    { toFun t := cylinder x₀' y₀' f' (z.1,a z.2 t)
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : (I × X) × I ↦ cylinder x₀' y₀' f' (z.1.1,a z.1.2 z.2))
    fun_prop

/-- Strict based structure squares descend to actual loops on the quotient cone. -/
def loopComparison : C(Space x₀ y₀ f, Path (point x₀' y₀' f') (point x₀' y₀' f')) :=
  desc x₀ y₀ f ((basedLoopMap (inr x₀' y₀' f') rfl).comp b)
    (cylinderLoop x₀' y₀' f' a)
    (fun x ↦ by
      ext t
      change cylinder x₀' y₀' f' (0,a x t) = inr x₀' y₀' f' (b (f x) t)
      rw [cylinder_zero]
      exact congrArg (inr x₀' y₀' f') (congrArg (fun p ↦ p t) (comm x)))
    (fun x ↦ by
      ext t
      change cylinder x₀' y₀' f' (1,a x t) = inr x₀' y₀' f' (b y₀ t)
      rw [cylinder_one, hb]
      rfl)
    (fun s ↦ by
      ext t
      change cylinder x₀' y₀' f' (s,a x₀ t) = inr x₀' y₀' f' (b y₀ t)
      rw [ha, hb]
      exact cylinder_base x₀' y₀' f' s)

@[simp] theorem loopComparison_point :
    loopComparison x₀ y₀ f x₀' y₀' f' hf' a b ha hb comm (point x₀ y₀ f) =
      Path.refl (point x₀' y₀' f') := by
  ext t
  change inr x₀' y₀' f' (b y₀ t) = point x₀' y₀' f'
  rw [hb]
  rfl

@[simp] theorem loopComparison_inr (y : Y) (t : I) :
    loopComparison x₀ y₀ f x₀' y₀' f' hf' a b ha hb comm (inr x₀ y₀ f y) t =
      inr x₀' y₀' f' (b y t) := rfl

@[simp] theorem loopComparison_cylinder (s : I) (x : X) (t : I) :
    loopComparison x₀ y₀ f x₀' y₀' f' hf' a b ha hb comm (cylinder x₀ y₀ f (s,x)) t =
      cylinder x₀' y₀' f' (s,a x t) := rfl

end Topology.ReducedMappingCone

namespace Topology.LoopPrespectrum
variable {E F : LoopPrespectrum.{u}} (f : E ⟶ F)

/-- The actual levelwise reduced mapping cone, with its constructed adjoint structure maps.
This is a prespectrum construction; an Omega property is not asserted. -/
def mappingCone : LoopPrespectrum.{u} where
  space n := TopCat.of (ReducedMappingCone.Space (E.point n) (F.point n) (f.map n))
  point n := ReducedMappingCone.point (E.point n) (F.point n) (f.map n)
  structureMap n := ReducedMappingCone.loopComparison (E.point n) (F.point n) (f.map n)
    (E.point (n+1)) (F.point (n+1)) (f.map (n+1)) (f.map_point (n+1))
    (E.structureMap n) (F.structureMap n) (E.map_point n) (F.map_point n) (f.comm n)
  map_point _n := ReducedMappingCone.loopComparison_point ..

/-- The original target embeds by a genuine morphism of prespectra. -/
def mappingConeInclusion : F ⟶ mappingCone f where
  map n := ReducedMappingCone.inr (E.point n) (F.point n) (f.map n)
  map_point n := rfl
  comm n x := by ext t; rfl

/-- Every component of the original composite has the displayed based nullhomotopy. -/
def mappingConeNullHomotopy (n : ℕ) :
    ((mappingConeInclusion f).map n |>.comp (f.map n)).HomotopyRel
      (ContinuousMap.const (E.space n) ((mappingCone f).point n)) {E.point n} :=
  ReducedMappingCone.nullHomotopy (E.point n) (F.point n) (f.map n) (f.map_point n)

/-- The cone contraction is coherent with every original structure map. -/
def mappingConeHomotopy : Homotopy (f ≫ mappingConeInclusion f) (zeroHom E (mappingCone f)) where
  level n := ReducedMappingCone.cylinder (E.point n) (F.point n) (f.map n)
  at_zero _n _x := ReducedMappingCone.cylinder_zero ..
  at_one _n _x := ReducedMappingCone.cylinder_one ..
  at_point _n _s := ReducedMappingCone.cylinder_base ..
  comm _n _s _x _t := rfl

variable {A B : Arrow LoopPrespectrum.{u}}

/-- Strict squares induce actual maps of the quotient-cone prespectra. -/
def mappingConeMap (sq : A ⟶ B) : mappingCone A.hom ⟶ mappingCone B.hom where
  map n := ReducedMappingCone.map (A.left.point n) (A.right.point n) (A.hom.map n)
    (B.left.point n) (B.right.point n) (B.hom.map n)
    (sq.left.map n) (sq.right.map n) (sq.left.map_point n) (sq.right.map_point n)
    (fun x ↦ congrArg (fun h ↦ h.map n x) sq.w.symm)
  map_point _n := ReducedMappingCone.map_point ..
  comm n q := by
    apply Path.ext
    funext t
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl y =>
        exact congrArg (ReducedMappingCone.inr (B.left.point (n+1)) (B.right.point (n+1))
          (B.hom.map (n+1))) (congrArg (fun p ↦ p t) (sq.right.comm n y))
      | inr z =>
        exact congrArg (fun y ↦ ReducedMappingCone.cylinder (B.left.point (n+1)) (B.right.point
          (n+1))
          (B.hom.map (n+1)) (z.1,y)) (congrArg (fun p ↦ p t) (sq.left.comm n z.2))

/-- Mapping cones form a functor on original strict arrow squares. -/
def mappingConeFunctor : Arrow LoopPrespectrum.{u} ⥤ LoopPrespectrum.{u} where
  obj A := mappingCone A.hom
  map := mappingConeMap
  map_id A := by
    apply Hom.ext
    funext n
    apply ReducedMappingCone.hom_ext <;> intro z <;> rfl
  map_comp sq sq' := by
    apply Hom.ext
    funext n
    apply ReducedMappingCone.hom_ext <;> intro z <;> rfl

end Topology.LoopPrespectrum

namespace Topology.LoopPrespectrum
variable {E F G : LoopPrespectrum.{u}} (f : E ⟶ F) (g : F ⟶ G)

/-- Actual coherent based nullhomotopies descend to maps of the constructed prespectra. -/
def mappingConeDesc (H : Homotopy (f ≫ g) (zeroHom E G)) : mappingCone f ⟶ G where
  map n := ReducedMappingCone.desc (E.point n) (F.point n) (f.map n) (g.map n) (H.level n)
    (H.at_zero n)
    (fun x ↦ (H.at_one n x).trans (g.map_point n).symm)
    (fun s ↦ (H.at_point n s).trans (g.map_point n).symm)
  map_point n := g.map_point n
  comm n q := by
    apply Path.ext
    funext t
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl y => exact congrArg (fun p ↦ p t) (g.comm n y)
      | inr z => exact H.comm n z.1 z.2 t

@[simp] theorem mappingConeInclusion_desc (H : Homotopy (f ≫ g) (zeroHom E G)) :
    mappingConeInclusion f ≫ mappingConeDesc f g H = g := by
  apply Hom.ext
  funext n
  ext x
  rfl

@[simp] theorem mappingConeDesc_cylinder (H : Homotopy (f ≫ g) (zeroHom E G))
    (n : ℕ) (s : unitInterval) (x : E.space n) :
    (mappingConeDesc f g H).map n (ReducedMappingCone.cylinder (E.point n) (F.point n) (f.map n)
      (s,x)) =
      H.level n (s,x) := rfl

/-- The original target and whole cylinder determine a prespectrum map uniquely. -/
theorem mappingCone_hom_ext {a b : mappingCone f ⟶ G}
    (hi : mappingConeInclusion f ≫ a = mappingConeInclusion f ≫ b)
    (hc : ∀ n s x, a.map n (ReducedMappingCone.cylinder (E.point n) (F.point n) (f.map n) (s, x)) =
      b.map n (ReducedMappingCone.cylinder (E.point n) (F.point n) (f.map n) (s, x))) : a = b := by
  apply Hom.ext
  funext n
  apply ReducedMappingCone.hom_ext
  · intro y
    exact congrArg (fun h ↦ h.map n y) hi
  · intro z
    exact hc n z.1 z.2

end Topology.LoopPrespectrum
