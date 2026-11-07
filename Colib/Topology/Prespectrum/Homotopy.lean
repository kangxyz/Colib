/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.Loop

/-!
# Coherent based homotopies of original prespectrum maps

Every continuous level homotopy preserves the base point and commutes with the original
structure maps at every time. Its time slices are genuine prespectrum morphisms, and its
induced original level homotopy maps agree. Precomposition and postcomposition retain
these exact homotopies.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/Homotopy.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, complete based tracks,
structure-map parameters and universe assumptions are retained. -/
@[expose] public section


noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum

/-- The actual pointwise zero map. -/
def zeroHom (E F : LoopPrespectrum.{u}) : E ⟶ F where
  map n := ContinuousMap.const _ (F.point n)
  map_point _ := rfl
  comm n x := by
    rw [show (ContinuousMap.const (E.space n) (F.point n)) x = F.point n from rfl, F.map_point]
    ext t
    rfl

/-- A based continuous homotopy whose every time slice is an original prespectrum map. -/
@[ext] structure Homotopy {E F : LoopPrespectrum.{u}} (f g : E ⟶ F) where
  /-- The based continuous homotopy at each prespectrum level. -/
  level (n : ℕ) : C(unitInterval × E.space n, F.space n)
  at_zero (n : ℕ) (x : E.space n) : level n (0,x) = f.map n x
  at_one (n : ℕ) (x : E.space n) : level n (1,x) = g.map n x
  at_point (n : ℕ) (s : unitInterval) : level n (s,E.point n) = F.point n
  comm (n : ℕ) (s : unitInterval) (x : E.space n) (t : unitInterval) :
    level (n+1) (s,E.structureMap n x t) = F.structureMap n (level n (s,x)) t

/-- The original time slice is genuinely a map of prespectra. -/
def Homotopy.at {E F : LoopPrespectrum.{u}} {f g : E ⟶ F} (H : Homotopy f g)
    (s : unitInterval) : E ⟶ F where
  map n := ⟨fun x ↦ H.level n (s,x), by fun_prop⟩
  map_point n := H.at_point n s
  comm n x := by ext t; exact H.comm n s x t

@[simp] theorem Homotopy.at_zero_eq {E F : LoopPrespectrum.{u}} {f g : E ⟶ F} (H : Homotopy f g) :
    H.at 0 = f := by
  apply Hom.ext
  funext n
  ext x
  exact H.at_zero n x

@[simp] theorem Homotopy.at_one_eq {E F : LoopPrespectrum.{u}} {f g : E ⟶ F} (H : Homotopy f g) :
    H.at 1 = g := by
  apply Hom.ext
  funext n
  ext x
  exact H.at_one n x

/-- The constant continuous homotopy retains every original structure square. -/
def Homotopy.refl {E F : LoopPrespectrum.{u}} (f : E ⟶ F) : Homotopy f f where
  level n := ⟨fun z ↦ f.map n z.2, by fun_prop⟩
  at_zero _n _x := rfl
  at_one _n _x := rfl
  at_point n _s := f.map_point n
  comm n _s x t := congrArg (fun p ↦ p t) (f.comm n x)

/-- Postcompose the whole coherent homotopy, with its original continuous maps. -/
def Homotopy.postcomp {E F G : LoopPrespectrum.{u}} {f g : E ⟶ F}
    (H : Homotopy f g) (h : F ⟶ G) : Homotopy (f ≫ h) (g ≫ h) where
  level n := (h.map n).comp (H.level n)
  at_zero n x := congrArg (h.map n) (H.at_zero n x)
  at_one n x := congrArg (h.map n) (H.at_one n x)
  at_point n s := (congrArg (h.map n) (H.at_point n s)).trans (h.map_point n)
  comm n s x t := (congrArg (h.map (n+1)) (H.comm n s x t)).trans
    (congrArg (fun p ↦ p t) (h.comm n (H.level n (s,x))))

/-- Precompose the whole coherent homotopy. -/
def Homotopy.precomp {D E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
    (h : D ⟶ E) (H : Homotopy f g) : Homotopy (h ≫ f) (h ≫ g) where
  level n := ⟨fun z ↦ H.level n (z.1,h.map n z.2), by fun_prop⟩
  at_zero n x := H.at_zero n (h.map n x)
  at_one n x := H.at_one n (h.map n x)
  at_point n s := by
    change H.level n (s,h.map n (D.point n)) = _; rw [h.map_point]; exact H.at_point n s
  comm n s x t := (congrArg (fun y ↦ H.level (n+1) (s,y))
      (congrArg (fun p ↦ p t) (h.comm n x))).trans (H.comm n s (h.map n x) t)

/-- Every level retains its original continuous homotopy relative to the base point. -/
def Homotopy.levelHomotopy {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
    (H : Homotopy f g) (n : ℕ) : (f.map n).HomotopyRel (g.map n) {E.point n} where
  toFun := H.level n
  continuous_toFun := (H.level n).continuous
  map_zero_left := H.at_zero n
  map_one_left := H.at_one n
  prop' s x hx := by
    have hx : x = E.point n := hx
    subst x
    exact (H.at_point n s).trans (f.map_point n).symm

/-- A coherent prespectrum homotopy preserves every original level homotopy map. -/
theorem Homotopy.homotopyGroupMap_eq {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
    (H : Homotopy f g) (n k : ℕ) :
    HomotopyGroup.map (N := Fin k) (f.map n) (f.map_point n) =
      HomotopyGroup.map (g.map n) (g.map_point n) :=
  HomotopyGroup.map_eq_of_based_homotopy _ _ (H.levelHomotopy n).toHomotopy (H.at_point n)

end Topology.LoopPrespectrum
