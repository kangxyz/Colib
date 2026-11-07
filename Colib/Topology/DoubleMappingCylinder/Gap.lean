/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.DoubleMappingCylinder.Basic
public import Colib.Topology.HomotopyPullback.Basic

/-!
# The original full-cylinder gap map

The source point a is sent to the right endpoint g(a), the left endpoint f(a), and the actual
stored path t↦l(a,t). The orientation agrees with the library's path-space homotopy pullback.
Every map in the original double-cylinder pushout is retained; no replacement is chosen.
-/

/-! Implementation provenance: adapted from
`Quillen/Topology/DoubleMappingCylinder/Gap.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, finite bounds,
whole path families and universe parameters are retained in their native owners. -/
@[expose] public section

noncomputable section
open Topology TopCat

open CategoryTheory Limits MonoidalCategory
open scoped Topology unitInterval

universe u

namespace TopCat.DoubleCylinder

variable {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
    {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
    (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)

/-- The original left endpoint map into the actual double cylinder. -/
def gapLeftEndpoint (e : TopCat.of (B ⊕ C) ⟶ D) : C(B, D) :=
  ⟨fun b ↦ e (Sum.inl b), e.hom.continuous.comp continuous_inl⟩

/-- The original right endpoint map into the actual double cylinder. -/
def gapRightEndpoint (e : TopCat.of (B ⊕ C) ⟶ D) : C(C, D) :=
  ⟨fun c ↦ e (Sum.inr c), e.hom.continuous.comp continuous_inr⟩

/-- The canonical original source-to-homotopy-pullback gap, using its full cylinder path. -/
def gap : C(A, HomotopyPullback (gapLeftEndpoint e) (gapRightEndpoint e)) where
  toFun a := ⟨(g a, f a, ⟨fun t ↦ l (a, ULift.up t),
    l.hom.continuous.comp (by fun_prop)⟩),
      ConcreteCategory.congr_hom sq.w (Sum.inl a), ConcreteCategory.congr_hom sq.w (Sum.inr a)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk g.hom.continuous
    apply Continuous.prodMk f.hom.continuous
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact l.hom.continuous.comp (by fun_prop)

/-- The stored path keeps the original source and cylinder coordinate exactly. -/
@[simp] theorem gap_path (a : A) (t : unitInterval) :
    (gap f g sq a).val.2.2 t = l (a, ULift.up t) := rfl

end TopCat.DoubleCylinder
