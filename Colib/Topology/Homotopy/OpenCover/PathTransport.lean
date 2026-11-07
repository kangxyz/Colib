/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.Independence

/-!
# Path Transport

Actual pointwise path equality transports its normalized value, with both
endpoint arrows explicit and overlap compatibility on the whole shared path.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set CategoryTheory
universe u v w z
namespace FundamentalGroupoid.OpenCover.ChartData
variable {X : Type u} [TopologicalSpace X] {ι : Type v} {U : ι → Set X}
variable {C : Type w} [Category.{z} C]
variable (d : ChartData (C := C) U)

/-- Actual pointwise path equality transports its normalized value, with both
endpoint arrows explicit and overlap compatibility on the whole shared path. -/
theorem localValue_path_congr (hc : d.Compatible)
    {x y x' y' : X} (p : Path x y) (q : Path x' y')
    (hx : x = x') (hy : y = y') (h : ∀ t, p t = q t)
    (i j : ι) (hi : Set.range p ⊆ U i) (hj : Set.range q ⊆ U j) :
    d.localValue i p hi = eqToHom (congrArg d.obj hx) ≫
      d.localValue j q hj ≫ eqToHom (congrArg d.obj hy.symm) := by
  subst x'
  subst y'
  have he : p = q := by ext t; exact h t
  subst q
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using hc i j p hi hj

/-- Pointwise equality of actual edges transports the whole finite ordered value. -/
theorem finitePathValue_transport (hc : d.Compatible) {n : ℕ}
    (a b : Fin (n + 1) → X) (e : ∀ j, a j = b j)
    (p : ∀ j : Fin n, Path (a j.castSucc) (a j.succ))
    (q : ∀ j : Fin n, Path (b j.castSucc) (b j.succ))
    (he : ∀ j t, p j t = q j t)
    (i k : Fin n → ι)
    (hi : ∀ j, Set.range (p j) ⊆ U (i j))
    (hk : ∀ j, Set.range (q j) ⊆ U (k j)) :
    finiteChainComp (fun j => d.obj (a j)) (fun j => d.localValue (i j) (p j) (hi j)) =
      eqToHom (congrArg d.obj (e 0)) ≫
      finiteChainComp (fun j => d.obj (b j)) (fun j => d.localValue (k j) (q j) (hk j)) ≫
      eqToHom (congrArg d.obj (e (Fin.last n)).symm) := by
  exact finiteChainComp_transport _ _ (fun j => congrArg d.obj (e j)) _ _
    (fun j => d.localValue_path_congr hc (p j) (q j) (e j.castSucc) (e j.succ)
      (he j) (i j) (k j) (hi j) (hk j))

end FundamentalGroupoid.OpenCover.ChartData
