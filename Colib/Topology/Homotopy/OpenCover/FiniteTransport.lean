/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.ValueEquality

/-!
# Finite Transport

Pointwise object transport commutes with the actual finite ordered product.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Set
universe u v w z
namespace FundamentalGroupoid.OpenCover

/-- Pointwise object transport commutes with the actual finite ordered product. -/
theorem finiteChainComp_transport {C : Type w} [Category.{z} C] {n : ℕ}
    (X Y : Fin (n + 1) → C) (e : ∀ j, X j = Y j)
    (f : ∀ j : Fin n, X j.castSucc ⟶ X j.succ)
    (g : ∀ j : Fin n, Y j.castSucc ⟶ Y j.succ)
    (hf : ∀ j, f j = eqToHom (e j.castSucc) ≫ g j ≫ eqToHom (e j.succ).symm) :
    finiteChainComp X f = eqToHom (e 0) ≫ finiteChainComp Y g ≫
      eqToHom (e (Fin.last n)).symm := by
  have h := (finiteChainCommSq X Y f g (fun j => eqToHom (e j)) (by
    intro j
    constructor
    rw [hf j]
    simp)).w
  apply (cancel_mono (eqToHom (e (Fin.last n)))).mp
  simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using h

variable {X : Type u} [TopologicalSpace X] {ι : Type v}
variable {C : Type w} [Category.{z} C] {U : ι → Set X}
namespace ChartData
variable (d : ChartData (C := C) U)

/-- Chart changes and equal parameter endpoints give exactly the two specified
object transports of the same actual affine path. -/
theorem localValue_subpath_congr (hc : d.Compatible) {x y : X} (p : Path x y)
    (i j : ι) (a b a' b' : unitInterval) (ha : a = a') (hb : b = b')
    (hi : Set.range (p.subpath a b) ⊆ U i) (hj : Set.range (p.subpath a' b') ⊆ U j) :
    d.localValue i (p.subpath a b) hi =
      eqToHom (congrArg (fun t => d.obj (p t)) ha) ≫
        d.localValue j (p.subpath a' b') hj ≫
          eqToHom (congrArg (fun t => d.obj (p t)) hb.symm) := by
  subst a'
  subst b'
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using hc i j _ hi hj

/-- Transport of a whole actual path subdivision under pointwise equal
parameter choices and arbitrary compatible chart labels. -/
theorem finiteSubpathValue_transport (hc : d.Compatible) {x y : X} (p : Path x y)
    {n : ℕ} (a b : Fin (n + 1) → unitInterval) (hab : ∀ j, a j = b j)
    (i k : Fin n → ι)
    (hi : ∀ j, Set.range (p.subpath (a j.castSucc) (a j.succ)) ⊆ U (i j))
    (hk : ∀ j, Set.range (p.subpath (b j.castSucc) (b j.succ)) ⊆ U (k j)) :
    finiteChainComp (fun j => d.obj (p (a j)))
      (fun j => d.localValue (i j) (p.subpath (a j.castSucc) (a j.succ)) (hi j)) =
    eqToHom (congrArg (fun t => d.obj (p t)) (hab 0)) ≫
      finiteChainComp (fun j => d.obj (p (b j)))
        (fun j => d.localValue (k j) (p.subpath (b j.castSucc) (b j.succ)) (hk j)) ≫
      eqToHom (congrArg (fun t => d.obj (p t)) (hab (Fin.last n)).symm) := by
  exact finiteChainComp_transport _ _ (fun j => congrArg (fun t => d.obj (p t)) (hab j))
    _ _ (fun j => d.localValue_subpath_congr hc p _ _ _ _ _ _
      (hab j.castSucc) (hab j.succ) (hi j) (hk j))

end ChartData
end FundamentalGroupoid.OpenCover
