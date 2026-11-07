/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.Prespectrum
public import Colib.Topology.Path.Separation
public import Colib.Topology.Realization.Skeleton

/-!
# Separation of the original iterated S-prespectrum

The actual simplicial realizations are T1. The degree-zero based-loop space
inherits T1 separation, so every original level of the iterated S-prespectrum
is T1, including the version using the proved small model.
-/
/-! Implementation provenance: `Quillen/Waldhausen/SConstruction/Iterated/Separation.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original maps, full null track, degree bounds, signed boundary and independent
object/hom universes are retained using the native strict chosen-zero subcategory. -/
@[expose] public section

open CategoryTheory
universe u v
namespace CategoryTheory.Waldhausen.IteratedS
open Topology SmallWaldhausenCategory

instance stageSpaceT1Space (r : ℕ) (W : WideSubcategory preservesZero.{u}) :
    T1Space (stageSpace r W) := by
  unfold stageSpace
  infer_instance

instance prespectrumSpaceT1Space (W : WideSubcategory preservesZero.{u}) (n : ℕ) :
    T1Space ((prespectrum W).space n) := by
  cases n with
  | zero =>
    change T1Space (Path (stagePoint 0 W) (stagePoint 0 W))
    infer_instance
  | succ r =>
    change T1Space (stageSpace r W)
    infer_instance

instance originalPrespectrumSpaceT1Space {C : Type u} [Category.{v} C]
    (W : Structure C) (n : ℕ) : T1Space ((originalPrespectrum W).space n) :=
  prespectrumSpaceT1Space (asSmallCategory W) n

end CategoryTheory.Waldhausen.IteratedS
