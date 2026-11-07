/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyPullback.Basic
public import Colib.Topology.UnitInterval
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Homotopy-cartesian product cells

The actual homotopy pullback of a product projection over an arbitrary base
map deformation retracts onto its ordinary pullback. Thus a homotopy
equivalence of fibers gives a canonical homotopy-cartesian product square,
without imposing local compactness, contractibility, or discreteness on
the base spaces. This is the geometric cell input for realization.
-/
/-! Implementation source: the lower topological section of
`Quillen/CategoryTheory/TheoremB/CartesianProducts.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. There is no categorical or Theorem B dependency. -/
@[expose] public section


noncomputable section

open scoped Topology unitInterval
open unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

namespace Topology.HomotopyPullback

variable {A B X : Type u} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X]
  (g : C(A, B))

/-- The ordinary pullback of a product projection includes by constant paths. -/
def productComparison : C(A × X, HomotopyPullback ((ContinuousMap.snd : C(X × B, B))) g) :=
  comparison _ _ (ContinuousMap.fst : C(A × X, A))
    ⟨fun z ↦ (z.2, g z.1), continuous_snd.prodMk (g.continuous.comp continuous_fst)⟩ rfl

/-- Forget the path and its moving initial basepoint. -/
def productRetraction : C(HomotopyPullback ((ContinuousMap.snd : C(X × B, B))) g, A × X) where
  toFun z := (z.1.1, z.1.2.1.1)
  continuous_toFun := by fun_prop

/-- Sliding the initial point to the path endpoint contracts the entire
path-space pullback continuously over the two retained coordinates. -/
def productContraction :
    (ContinuousMap.id (HomotopyPullback ((ContinuousMap.snd : C(X × B, B))) g)).Homotopy
      ((productComparison (X := X) g).comp (productRetraction g)) where
  toFun z := ⟨(z.2.1.1, (z.2.1.2.1.1, z.2.1.2.2 z.1),
    ⟨fun t ↦ z.2.1.2.2 (σ (σ z.1 * σ t)), z.2.1.2.2.continuous.comp (by fun_prop)⟩),
    by simp, by simpa using z.2.2.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · apply Continuous.prodMk
      · fun_prop
      · apply ContinuousMap.continuous_of_continuous_uncurry
        change Continuous (fun z : (I × HomotopyPullback ((ContinuousMap.snd : C(X × B, B))) g) × I
          ↦
          z.1.2.1.2.2 (σ (σ z.1.1 * σ z.2)))
        fun_prop
  map_zero_left z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · apply Prod.ext
        · rfl
        · exact z.2.1
      · apply ContinuousMap.ext
        intro t
        change z.1.2.2 (σ (σ 0 * σ t)) = z.1.2.2 t
        simp
  map_one_left z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · apply Prod.ext
        · rfl
        · exact z.2.2
      · apply ContinuousMap.ext
        intro t
        change z.1.2.2 (σ (σ 1 * σ t)) = g z.1.1
        simpa using z.2.2

/-- The path contraction fixes the entire canonical ordinary pullback. -/
@[simp]
theorem productContraction_comparison (t : I) (x : A × X) :
    productContraction g (t, productComparison g x) = productComparison g x := rfl

/-- A product projection has its ordinary pullback as an actual homotopy
pullback, with the canonical constant-path inclusion as forward map. -/
def productHomotopyEquiv : ContinuousMap.HomotopyEquiv (A × X)
    (HomotopyPullback ((ContinuousMap.snd : C(X × B, B))) g) where
  toFun := productComparison g
  invFun := productRetraction g
  left_inv := ContinuousMap.Homotopic.refl _
  right_inv := ⟨(productContraction g).symm⟩

@[simp]
theorem productHomotopyEquiv_toFun :
    (productHomotopyEquiv (X := X) g).toFun = productComparison g := rfl

/-- A fiber homotopy equivalence makes the product square over any base
map homotopy cartesian. -/
def fiberProductHomotopyEquiv {Y : Type u} [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) :
    ContinuousMap.HomotopyEquiv (A × X)
      (HomotopyPullback (ContinuousMap.snd : C(Y × B, B)) g) :=
  ((ContinuousMap.HomotopyEquiv.refl A).prodCongr e).trans (productHomotopyEquiv g)

/-- The product-square equivalence has the prescribed fiber map and base
map, with an actual constant path. -/
@[simp]
theorem fiberProductHomotopyEquiv_apply {Y : Type u} [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (z : A × X) :
    fiberProductHomotopyEquiv g e z =
      ⟨(z.1, (e z.2, g z.1), ContinuousMap.const I (g z.1)), rfl, rfl⟩ := rfl

/-- Pulling back the identity along any continuous map has the source as
its homotopy type, via the canonical constant-path comparison. -/
def identityHomotopyEquiv :
    ContinuousMap.HomotopyEquiv A (HomotopyPullback (ContinuousMap.id B) g) :=
  (((Homeomorph.prodUnique A PUnit).symm.toHomotopyEquiv).trans
    (productHomotopyEquiv (X := PUnit) g)).trans
      (sourceHomeomorph (ContinuousMap.id B) g (Homeomorph.uniqueProd PUnit B)).toHomotopyEquiv

@[simp]
theorem identityHomotopyEquiv_toFun :
    (identityHomotopyEquiv g).toFun = comparison (ContinuousMap.id B) g
      (ContinuousMap.id A) g rfl := rfl

section Products

variable {X₁ X₂ A₁ A₂ B₁ B₂ : Type u}
  [TopologicalSpace X₁] [TopologicalSpace X₂]
  [TopologicalSpace A₁] [TopologicalSpace A₂]
  [TopologicalSpace B₁] [TopologicalSpace B₂]
  (f₁ : C(X₁, B₁)) (f₂ : C(X₂, B₂)) (g₁ : C(A₁, B₁)) (g₂ : C(A₂, B₂))

/-- Actual path-space homotopy pullbacks commute homeomorphically with
products; the two path coordinates are paired pointwise. -/
def prodHomeomorph :
    HomotopyPullback f₁ g₁ × HomotopyPullback f₂ g₂ ≃ₜ
      HomotopyPullback (f₁.prodMap f₂) (g₁.prodMap g₂) where
  toFun z := ⟨((z.1.1.1, z.2.1.1), (z.1.1.2.1, z.2.1.2.1),
    z.1.1.2.2.prodMk z.2.1.2.2),
    Prod.ext z.1.2.1 z.2.2.1, Prod.ext z.1.2.2 z.2.2.2⟩
  invFun z :=
    (⟨(z.1.1.1, z.1.2.1.1, ContinuousMap.fst.comp z.1.2.2),
      congrArg Prod.fst z.2.1, congrArg Prod.fst z.2.2⟩,
     ⟨(z.1.1.2, z.1.2.1.2, ContinuousMap.snd.comp z.1.2.2),
      congrArg Prod.snd z.2.1, congrArg Prod.snd z.2.2⟩)
  left_inv z := rfl
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply ContinuousMap.ext
        intro t
        rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · apply Continuous.prodMk
      · fun_prop
      · apply ContinuousMap.continuous_of_continuous_uncurry
        exact (by fun_prop : Continuous fun z :
          (HomotopyPullback f₁ g₁ × HomotopyPullback f₂ g₂) × I ↦
          (z.1.1.1.2.2 z.2, z.1.2.1.2.2 z.2))
  continuous_invFun := by
    apply Continuous.prodMk
    all_goals
      apply Continuous.subtype_mk
      apply Continuous.prodMk
      · fun_prop
      · apply Continuous.prodMk
        · fun_prop
        · apply ContinuousMap.continuous_of_continuous_uncurry
          fun_prop

/-- The product homeomorphism preserves the canonical comparisons of
strictly commuting squares exactly. -/
theorem prodHomeomorph_comparison
    {W₁ W₂ : Type u} [TopologicalSpace W₁] [TopologicalSpace W₂]
    (a₁ : C(W₁, A₁)) (a₂ : C(W₂, A₂))
    (h₁ : C(W₁, X₁)) (h₂ : C(W₂, X₂))
    (c₁ : f₁.comp h₁ = g₁.comp a₁) (c₂ : f₂.comp h₂ = g₂.comp a₂)
    (z : W₁ × W₂) :
    prodHomeomorph f₁ f₂ g₁ g₂
      (comparison f₁ g₁ a₁ h₁ c₁ z.1, comparison f₂ g₂ a₂ h₂ c₂ z.2) =
      comparison (f₁.prodMap f₂) (g₁.prodMap g₂) (a₁.prodMap a₂) (h₁.prodMap h₂)
        (ContinuousMap.ext fun x ↦ Prod.ext (ContinuousMap.congr_fun c₁ x.1)
          (ContinuousMap.congr_fun c₂ x.2)) z := rfl

end Products

end Topology.HomotopyPullback
