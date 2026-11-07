/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.FiberwiseMappingPath.BaseChangeLifting

/-! # Vertical endpoint lifting through an injective change of displayed base

Only the proof of verticality changes: the source and every stored path
value remain literally the same. The ambient base need not have HLP.


Implementation provenance:
`Quillen/Topology/FiberwiseMappingPath/InjectiveBaseLifting.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open scoped Topology unitInterval
universe u v w z
namespace Topology.FiberwiseMappingPath
variable {E : Type u} {F : Type v} {B : Type w} {T : Type z}
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B] [TopologicalSpace T]

/-- An injective base inclusion reflects the complete stored-path condition. -/
def injectiveBaseHomeomorph (q : C(F, B)) (f : C(E, F)) (j : C(B, T))
    (hj : Function.Injective j) : Space (j.comp q) f ≃ₜ Space q f :=
  Homeomorph.setCongr (by
    ext x
    change (x.2 0 = f x.1 ∧ ∀ t,j (q (x.2 t)) = j (q (f x.1))) ↔
      x.2 0 = f x.1 ∧ ∀ t,q (x.2 t) = q (f x.1)
    exact and_congr_right (fun _ ↦ forall_congr' (fun _ ↦ hj.eq_iff)))

@[simp] theorem injectiveBaseHomeomorph_path (q : C(F, B)) (f : C(E, F))
    (j : C(B, T)) (hj : Function.Injective j) (x : Space (j.comp q) f) (t : unitInterval) :
    (injectiveBaseHomeomorph q f j hj x).val.2 t = x.val.2 t := rfl

/-- Endpoint boundary lifting transfers without changing any boundary path. -/
theorem endpoint_boundaryLifting_of_injective_base (q : C(F, B)) (f : C(E, F))
    (j : C(B, T)) (hj : Function.Injective j)
    (h : CubicalSubdivision.BoundaryLifting (endpoint q f)) :
    CubicalSubdivision.BoundaryLifting (endpoint (j.comp q) f) := by
  intro n a b hab
  let e := injectiveBaseHomeomorph q f j hj
  obtain ⟨l, hl, hb⟩ := h n (e.toHomotopyEquiv.toFun.comp a) b hab
  refine ⟨e.symm.toHomotopyEquiv.toFun.comp l, ?_, ?_⟩
  · intro x
    change e.symm (l x.val) = a x
    rw [hl x]
    exact e.symm_apply_apply (a x)
  · exact hb

end Topology.FiberwiseMappingPath
