/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.Loop.DegreeShift
public import Mathlib.Topology.Category.TopCat.Basic

/-!
# Sequential loop prespectra

A sequential loop prespectrum consists of actual pointed topological spaces and continuous
based maps from each space to the loop space of its successor. This owner constructs their
category with strictly commuting original structure maps. No weak equivalence condition on
those maps is included.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/Loop.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, assumptions,
chosen zero objects and universe parameters are retained. -/
@[expose] public section


noncomputable section
open CategoryTheory
open scoped Topology
universe u
namespace Topology

/-- A genuine sequential prespectrum in adjoint form: actual based spaces
and actual continuous based maps to the loops on the next space. There is
no Omega-equivalence or stable-homotopy property among its fields. -/
structure LoopPrespectrum where
  /-- The topological space in each prespectrum degree. -/
  space : ℕ → TopCat.{u}
  /-- The chosen point in each prespectrum degree. -/
  point (n : ℕ) : space n
  /-- The based map to loops on the next prespectrum space. -/
  structureMap (n : ℕ) : C(space n, Path (point (n+1)) (point (n+1)))
  map_point (n : ℕ) : structureMap n (point n) = Path.refl (point (n+1))

/-- Morphisms retain the original level maps and the exact loop-structure square. -/
@[ext] structure LoopPrespectrum.Hom (E F : LoopPrespectrum.{u}) where
  /-- The continuous based map in each prespectrum degree. -/
  map (n : ℕ) : C(E.space n, F.space n)
  map_point (n : ℕ) : map n (E.point n) = F.point n
  comm (n : ℕ) (x : E.space n) :
    basedLoopMap (map (n+1)) (map_point (n+1)) (E.structureMap n x) =
      F.structureMap n (map n x)

namespace LoopPrespectrum

/-- The identity morphism of a loop prespectrum. -/
def Hom.id (E : LoopPrespectrum.{u}) : Hom E E where
  map _ := ContinuousMap.id _
  map_point _ := rfl
  comm _ _ := by ext t; rfl

/-- Composition of loop-prespectrum morphisms, defined by levelwise composition. -/
def Hom.comp {E F G : LoopPrespectrum.{u}} (f : Hom E F) (g : Hom F G) : Hom E G where
  map n := (g.map n).comp (f.map n)
  map_point n := (congrArg (g.map n) (f.map_point n)).trans (g.map_point n)
  comm n x := by
    calc
      basedLoopMap ((g.map (n+1)).comp (f.map (n+1))) _ (E.structureMap n x) =
          basedLoopMap (g.map (n+1)) (g.map_point (n+1))
            (basedLoopMap (f.map (n+1)) (f.map_point (n+1)) (E.structureMap n x)) := by ext t; rfl
      _ = basedLoopMap (g.map (n+1)) (g.map_point (n+1)) (F.structureMap n (f.map n x)) :=
        congrArg _ (f.comm n x)
      _ = G.structureMap n (g.map n (f.map n x)) := g.comm n (f.map n x)

instance : Category LoopPrespectrum.{u} where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by apply Hom.ext; funext n; ext x; rfl
  comp_id f := by apply Hom.ext; funext n; ext x; rfl
  assoc f g h := by apply Hom.ext; funext n; ext x; rfl

end LoopPrespectrum

end Topology
