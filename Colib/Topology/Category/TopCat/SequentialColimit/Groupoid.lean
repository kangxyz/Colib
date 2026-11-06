/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.Topology.Category.TopCat.Basic

/-!
# Groupoid

The given actual successor restrictions compose to an actual restriction
natural isomorphism for every finite transition, retaining all endpoint transports.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopCat
universe u v w
namespace FundamentalGroupoid.SequentialColimit
variable {F : ℕ ⥤ TopCat.{u}} {C : Type v} [Category.{w} C]
    (D : ∀ n, FundamentalGroupoid (F.obj n) ⥤ C)
    (e : ∀ n, FundamentalGroupoid.map (F.map (homOfLE (Nat.le_succ n))).hom ⋙ D (n + 1) ≅ D n)

/-- The given actual successor restrictions compose to an actual restriction
natural isomorphism for every finite transition, retaining all endpoint transports. -/
def stageComparison {k n : ℕ} (h : k ≤ n) :
    FundamentalGroupoid.map (F.map (homOfLE h)).hom ⋙ D n ≅ D k := by
  induction h using Nat.leRec with
  | refl =>
    apply eqToIso
    have hm : (F.map (homOfLE (Nat.le_refl k))).hom = ContinuousMap.id (F.obj k) := by
      change (F.map (𝟙 k)).hom = _
      rw [F.map_id]
      rfl
    rw [hm, FundamentalGroupoid.map_id]
    rfl
  | @le_succ_of_le n h ih =>
    have hm : (F.map (homOfLE (Nat.le_succ_of_le h))).hom =
        (F.map (homOfLE (Nat.le_succ n))).hom.comp (F.map (homOfLE h)).hom := by
      change (F.map _).hom = (F.map _ ≫ F.map _).hom
      rw [← F.map_comp]
      rfl
    have heq : FundamentalGroupoid.map (F.map (homOfLE (Nat.le_succ_of_le h))).hom ⋙
        D (n + 1) = FundamentalGroupoid.map (F.map (homOfLE h)).hom ⋙
          (FundamentalGroupoid.map (F.map (homOfLE (Nat.le_succ n))).hom ⋙ D (n + 1)) := by
      rw [hm, FundamentalGroupoid.map_comp, Functor.assoc]
    exact eqToIso heq ≪≫
      Functor.isoWhiskerLeft (FundamentalGroupoid.map (F.map (homOfLE h)).hom) (e n) ≪≫ ih

include e in
/-- Equality of later-stage values reflects to earlier decoder values, by the
constructed natural endpoint transports, without a faithfulness hypothesis. -/
theorem decoder_value_eq_of_later {k n : ℕ} (h : k ≤ n) {x y : F.obj k} (p q : Path x y)
    (hm : (D n).map (Path.Homotopic.Quotient.mk
        (p.map (F.map (homOfLE h)).hom.continuous)) =
      (D n).map (Path.Homotopic.Quotient.mk
        (q.map (F.map (homOfLE h)).hom.continuous))) :
    (D k).map (Path.Homotopic.Quotient.mk p) = (D k).map (Path.Homotopic.Quotient.mk q) := by
  let E := stageComparison D e h
  apply (cancel_epi (E.hom.app (FundamentalGroupoid.mk x))).mp
  have hp := E.hom.naturality (Path.Homotopic.Quotient.mk p)
  have hq := E.hom.naturality (Path.Homotopic.Quotient.mk q)
  change (D n).map (Path.Homotopic.Quotient.mk
      (p.map (F.map (homOfLE h)).hom.continuous)) ≫ E.hom.app (FundamentalGroupoid.mk y) = _ at hp
  change (D n).map (Path.Homotopic.Quotient.mk
      (q.map (F.map (homOfLE h)).hom.continuous)) ≫ E.hom.app (FundamentalGroupoid.mk y) = _ at hq
  exact hp.symm.trans ((congrArg (fun f => f ≫ E.hom.app (FundamentalGroupoid.mk y)) hm).trans hq)

end FundamentalGroupoid.SequentialColimit
