/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Homotopy.HomotopyGroup.Product
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalenceProperty

/-! # Complete weak equivalences for literal topological product maps

Actual generalized loops and their full relative homotopies pair pointwise.
This proves the projection-pair bijection also in degree zero. Strict
naturality and actual paired component paths then prove the complete weak
property of the original product map, with empty factors included.


Implementation provenance:
`Quillen/Topology/HomotopyGroups/ProductWeakEquivalence.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open scoped Topology unitInterval
universe w u v u' v'
namespace Topology
variable {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']

/-- The original pair of projection maps on arbitrary generalized homotopy
sets, including the empty-index (zero-dimensional) homotopy set. -/
def homotopyProdMap (N : Type w) (x : X) (y : Y) :
    HomotopyGroup N (X × Y) (x,y) → HomotopyGroup N X x × HomotopyGroup N Y y :=
  fun a ↦ (HomotopyGroup.map ContinuousMap.fst rfl a,
    HomotopyGroup.map ContinuousMap.snd rfl a)

/-- Actual loop pairing and full-boundary homotopy pairing prove bijectivity
without any nonempty-index or connectedness hypothesis. -/
theorem homotopyProdMap_bijective (N : Type w) (x : X) (y : Y) :
    Function.Bijective (homotopyProdMap N x y) := by
  constructor
  · intro a b hab
    induction a using Quotient.inductionOn with | h p =>
      induction b using Quotient.inductionOn with | h q =>
        have h₁ := congrArg _root_.Prod.fst hab
        have h₂ := congrArg _root_.Prod.snd hab
        change Quotient.mk' (GenLoop.postcomp ContinuousMap.fst rfl p) =
          Quotient.mk' (GenLoop.postcomp ContinuousMap.fst rfl q) at h₁
        change Quotient.mk' (GenLoop.postcomp ContinuousMap.snd rfl p) =
          Quotient.mk' (GenLoop.postcomp ContinuousMap.snd rfl q) at h₂
        obtain ⟨H₁⟩ := Quotient.exact h₁
        obtain ⟨H₂⟩ := Quotient.exact h₂
        let H : p.val.HomotopyRel q.val (Cube.boundary N) := {
          toHomotopy := H₁.toHomotopy.prodMk H₂.toHomotopy
          prop' t z hz := _root_.Prod.ext (H₁.eq_fst t hz) (H₂.eq_fst t hz) }
        exact Quotient.sound ⟨H⟩
  · rintro ⟨a,b⟩
    induction a using Quotient.inductionOn with | h p =>
      induction b using Quotient.inductionOn with | h q =>
        let r : GenLoop N (X × Y) (x,y) :=
          ⟨p.val.prodMk q.val, fun t ht ↦ _root_.Prod.ext
            (GenLoop.boundary p t ht) (GenLoop.boundary q t ht)⟩
        refine ⟨Quotient.mk' r, ?_⟩
        apply _root_.Prod.ext
        · apply congrArg Quotient.mk'
          ext t
          rfl
        · apply congrArg Quotient.mk'
          ext t
          rfl

/-- Positive dimensions agree literally with the already established pair
of original group-homomorphism projections. -/
@[simp] theorem homotopyProdMap_succ (n : ℕ) (x : X) (y : Y) :
    homotopyProdMap (Fin (n + 1)) x y = (piProdMap n x y : _ → _) := rfl

/-- Strict naturality under the literal product continuous map. -/
theorem homotopyProdMap_naturality (N : Type w) (f : C(X, X')) (g : C(Y, Y'))
    (x : X) (y : Y) (a : HomotopyGroup N (X × Y) (x, y)) :
    homotopyProdMap N (f x) (g y) (HomotopyGroup.map (f.prodMap g) rfl a) =
      _root_.Prod.map (HomotopyGroup.map f (x := x) rfl)
        (HomotopyGroup.map g (x := y) rfl) (homotopyProdMap N x y a) := by
  induction a using Quotient.inductionOn with | h p => rfl

/-- Complete weak equivalences are preserved by the original ordinary
product map, including component surjectivity and all empty-factor cases. -/
theorem IsWeakHomotopyEquivalence.prodMap {f : C(X, X')} {g : C(Y, Y')}
    (hf : IsWeakHomotopyEquivalence f) (hg : IsWeakHomotopyEquivalence g) :
    IsWeakHomotopyEquivalence (f.prodMap g) where
  component_surjective := by
    rintro ⟨x',y'⟩
    obtain ⟨x,⟨γ⟩⟩ := hf.component_surjective x'
    obtain ⟨y,⟨δ⟩⟩ := hg.component_surjective y'
    exact ⟨(x,y),⟨γ.prod δ⟩⟩
  homotopy_bijective := by
    rintro ⟨x,y⟩ n
    let p := HomotopyGroup.map (N := Fin n) f (x := x) rfl
    let q := HomotopyGroup.map (N := Fin n) g (x := y) rfl
    have hp : Function.Bijective p := hf.homotopy_bijective x n
    have hq : Function.Bijective q := hg.homotopy_bijective y n
    have hpq : Function.Bijective (_root_.Prod.map p q) := by
      constructor
      · intro a b h
        exact _root_.Prod.ext (hp.injective (congrArg _root_.Prod.fst h))
          (hq.injective (congrArg _root_.Prod.snd h))
      · rintro ⟨a,b⟩
        obtain ⟨a',ha⟩ := hp.surjective a
        obtain ⟨b',hb⟩ := hq.surjective b
        exact ⟨(a',b'), _root_.Prod.ext ha hb⟩
    have heq : homotopyProdMap (Fin n) (f x) (g y) ∘
        HomotopyGroup.map (N := Fin n) (f.prodMap g) (x := (x,y)) rfl =
        (_root_.Prod.map p q) ∘ homotopyProdMap (Fin n) x y := by
      funext a
      exact homotopyProdMap_naturality (Fin n) f g x y a
    have hcomp : Function.Bijective (homotopyProdMap (Fin n) (f x) (g y) ∘
        HomotopyGroup.map (N := Fin n) (f.prodMap g) (x := (x,y)) rfl) := by
      rw [heq]
      exact hpq.comp (homotopyProdMap_bijective (Fin n) x y)
    exact (Function.Bijective.of_comp_iff'
      (homotopyProdMap_bijective (Fin n) (f x) (g y)) _).1 hcomp

/-- The literal left-factor weak map, with an arbitrary untouched factor. -/
theorem IsWeakHomotopyEquivalence.prodMap_id {f : C(X, X')}
    (hf : IsWeakHomotopyEquivalence f) (Y : Type v) [TopologicalSpace Y] :
    IsWeakHomotopyEquivalence (f.prodMap (ContinuousMap.id Y)) :=
  hf.prodMap (isWeakHomotopyEquivalence_id Y)

/-- The literal right-factor weak map, with an arbitrary untouched factor. -/
theorem IsWeakHomotopyEquivalence.id_prodMap {g : C(Y, Y')}
    (hg : IsWeakHomotopyEquivalence g) (X : Type u) [TopologicalSpace X] :
    IsWeakHomotopyEquivalence ((ContinuousMap.id X).prodMap g) :=
  (isWeakHomotopyEquivalence_id X).prodMap hg

end Topology
