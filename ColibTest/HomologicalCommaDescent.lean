/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.CategoryTheory.TheoremA.InitialHomology

/-! # Original comma maps with their actual pulled-back local systems -/

open CategoryTheory Limits TheoremA FundamentalGroupoid.LocalCoefficients
open scoped Simplicial Topology

universe u
noncomputable section

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (F : C ⥤ D) (i : D) (hi : IsInitial i)
  (htrans : ∀ (d : D) (B : System.{u, u} |(commaNerveDiagram F).obj d|),
    AbelianMonodromy B → QuasiIso (pushforwardChainMap
      (SSet.toTop.map ((commaNerveDiagram F).map (hi.to d))).hom B))

example (A : System.{u, u} |replacementDiagonal (commaNerveDiagram F)|)
    (hA : AbelianMonodromy A) :
    QuasiIso (pushforwardChainMap
      (SSet.toTop.map (replacementEntry (commaNerveDiagram F) i)).hom A) :=
  commaInitialReplacementEntry_abelian_quasiIso F i hi htrans A hA

example (A : System.{u, u} (ClassifyingSpace C)) (hA : AbelianMonodromy A) (n : ℕ) :
    IsIso (pushforwardHomologyMap
      (SSet.toTop.map (nerveMap (CostructuredArrow.proj F i))).hom A n) := by
  have := commaInitialProjection_abelian_quasiIso F i hi htrans A hA
  change IsIso (HomologicalComplex.homologyMap _ n)
  infer_instance
