/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.RankedChain.Order
public import Colib.CategoryTheory.ComposableArrows.Append

/-!
# Strict append and extension into an existing terminal vertex

A genuinely rank-increasing terminal arrow appends an actual strict chain.
All old data and the complete terminal arrow are retained. An exact face A→B
which misses B's last vertex extends to an exact face from the append of A
into B itself. This handles the essential mixed append/compression case, not
merely the easier situation in which both source and target are appended.

Implementation provenance:
`Quillen/CategoryTheory/RankedChain/Append.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses and universe parameters are retained.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open CategoryTheory.SemisimplexResolution CategoryTheory.ComposableArrows
universe u

namespace CategoryTheory.RankedChainOrder
variable (C : Type u) [SmallCategory C] (rank : C → ℕ)

/-- A rank-increasing terminal arrow appends an actual nondegenerate chain. -/
def append (A : Obj C rank) {Y : C} (q : A.chain.obj (Fin.last A.dim) ⟶ Y)
    (hq : rank (A.chain.obj (Fin.last A.dim)) < rank Y) : Obj C rank where
  dim := A.dim + 1
  chain := appendChain A.chain q
  strict := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa only [appendChain_obj_castSucc, Fin.succ_last, appendChain_obj_last] using hq
    · rw [← Fin.castSucc_succ]
      simp only [appendChain_obj_castSucc]
      exact A.strict (Fin.castSucc_lt_succ (i := j))

/-- The append face is strict equality of the complete original functor. -/
theorem append_restriction (A : Obj C rank) {Y : C}
    (q : A.chain.obj (Fin.last A.dim) ⟶ Y) :
    Fin.castSuccFunctor (A.dim + 1) ⋙ appendChain A.chain q = A.chain := by
  refine CategoryTheory.Functor.ext (fun i ↦ appendChain_obj_castSucc A.chain q i) ?_
  intro i j f
  change (appendChain A.chain q).map ((Fin.castSuccFunctor (A.dim + 1)).map f) =
    eqToHom (appendChain_obj_castSucc A.chain q i) ≫ A.chain.map f ≫
      eqToHom (appendChain_obj_castSucc A.chain q j).symm
  have h := (appendChainRestrictionIso A.chain q).hom.naturality f
  change (appendChain A.chain q).map ((Fin.castSuccFunctor (A.dim + 1)).map f) ≫
    eqToHom (appendChain_obj_castSucc A.chain q j) =
      eqToHom (appendChain_obj_castSucc A.chain q i) ≫ A.chain.map f at h
  simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using
    congrArg (fun k ↦ k ≫ eqToHom (appendChain_obj_castSucc A.chain q j).symm) h

/-- The original chain embeds as an actual face of its nondegenerate append. -/
def appendFace (A : Obj C rank) {Y : C}
    (q : A.chain.obj (Fin.last A.dim) ⟶ Y)
    (hq : rank (A.chain.obj (Fin.last A.dim)) < rank Y) :
    Face C rank A (append C rank A q hq) :=
  ⟨(Fin.castSuccOrderEmb (n := A.dim + 1)), append_restriction C rank A q⟩

/-- A single original object, as a strict chain of length zero. -/
def vertex (X : C) : Obj C rank where
  dim := 0
  chain := ComposableArrows.mk₀ X
  strict := by intro i j hij; exact False.elim (by have := i.isLt; have := j.isLt; omega)

/-- The unique index map from a vertex to a chosen chain occurrence. -/
def vertexIndex {n : ℕ} (i : Fin (n + 1)) : Fin 1 ↪o Fin (n + 1) :=
  OrderEmbedding.ofStrictMono (fun _ ↦ i) (by
    intro a b hab
    have := a.isLt
    have := b.isLt
    omega)

/-- The original vertex appears as a literal face of the original chain. -/
def vertexFace (A : Obj C rank) (i : Fin (A.dim + 1)) :
    Face C rank (vertex C rank (A.chain.obj i)) A where
  index := vertexIndex i
  face := by
    refine CategoryTheory.Functor.ext
      (F := (vertexIndex i).monotone.functor ⋙ A.chain)
      (G := (vertex C rank (A.chain.obj i)).chain) (fun _ ↦ rfl) ?_
    intro a b f
    have hab : a = b := Subsingleton.elim _ _
    subst b
    have hf : f = 𝟙 a := Subsingleton.elim _ _
    subst f
    simp

end CategoryTheory.RankedChainOrder

namespace CategoryTheory.RankedChainOrder
variable (C : Type u) [SmallCategory C] (rank : C → ℕ)
variable {A B : Obj C rank} (f : Face C rank A B)

/-- The original face's exact object equality. -/
theorem Face.obj_eq (i : Fin (A.dim + 1)) : B.chain.obj (f.index i) = A.chain.obj i :=
  congrArg (fun T : ComposableArrows C A.dim ↦ T.obj i) f.face

/-- The original last-vertex map associated to an exact face. -/
def Face.lastMap : A.chain.obj (Fin.last A.dim) ⟶ B.chain.obj (Fin.last B.dim) :=
  eqToHom (f.obj_eq C rank (Fin.last A.dim)).symm ≫
    B.chain.map (homOfLE (Fin.le_last (f.index (Fin.last A.dim))))

/-- If the source misses the target's last vertex, its last rank is smaller. -/
theorem Face.lastRank_lt (hi : f.index (Fin.last A.dim) < Fin.last B.dim) :
    rank (A.chain.obj (Fin.last A.dim)) < rank (B.chain.obj (Fin.last B.dim)) := by
  rw [← f.obj_eq C rank (Fin.last A.dim)]
  exact B.strict hi

/-- Extend the original index embedding by the target's actual last index. -/
def Face.appendIndex (hi : f.index (Fin.last A.dim) < Fin.last B.dim) :
    Fin (A.dim + 1 + 1) ↪o Fin (B.dim + 1) :=
  OrderEmbedding.ofStrictMono (Fin.lastCases (Fin.last B.dim) f.index) (by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa only [Fin.lastCases_castSucc, Fin.succ_last, Fin.lastCases_last] using hi
    · rw [← Fin.castSucc_succ]
      simp only [Fin.lastCases_castSucc]
      exact f.index.strictMono (Fin.castSucc_lt_succ (i := j)))

@[simp] theorem Face.appendIndex_castSucc
    (hi : f.index (Fin.last A.dim) < Fin.last B.dim) (i : Fin (A.dim + 1)) :
    f.appendIndex C rank hi i.castSucc = f.index i := by simp [Face.appendIndex]

@[simp] theorem Face.appendIndex_last
    (hi : f.index (Fin.last A.dim) < Fin.last B.dim) :
    f.appendIndex C rank hi (Fin.last (A.dim + 1)) = Fin.last B.dim := by
  simp [Face.appendIndex]

/-- The full old restriction of the extended index is the original index. -/
theorem Face.appendIndex_restriction
    (hi : f.index (Fin.last A.dim) < Fin.last B.dim) :
    Fin.castSuccFunctor (A.dim + 1) ⋙ (f.appendIndex C rank hi).monotone.functor =
      f.index.monotone.functor := by
  exact CategoryTheory.Functor.ext (f.appendIndex_castSucc C rank hi)

/-- The extended original face agrees with the appended chain on all objects. -/
theorem Face.append_obj_eq (hi : f.index (Fin.last A.dim) < Fin.last B.dim)
    (i : Fin (A.dim + 1 + 1)) :
    B.chain.obj (f.appendIndex C rank hi i) =
      (append C rank A (f.lastMap C rank) (f.lastRank_lt C rank hi)).chain.obj i := by
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [Face.appendIndex, append, appendChain_obj_last]
  · simp only [Face.appendIndex, OrderEmbedding.coe_ofStrictMono, Fin.lastCases_castSucc]
    change B.chain.obj (f.index j) = (appendChain A.chain (f.lastMap C rank)).obj j.castSucc
    rw [appendChain_obj_castSucc]
    exact f.obj_eq C rank j

/-- The extended index's final arrow retains the old-to-last original arrow. -/
theorem Face.appendIndex_map_to_last
    (hi : f.index (Fin.last A.dim) < Fin.last B.dim) :
    (f.appendIndex C rank hi).monotone.functor.map
        (homOfLE (Fin.le_last (Fin.last A.dim).castSucc)) =
      eqToHom (f.appendIndex_castSucc C rank hi (Fin.last A.dim)) ≫
        homOfLE (Fin.le_last (f.index (Fin.last A.dim))) ≫
        eqToHom (f.appendIndex_last C rank hi).symm := Subsingleton.elim _ _

/-- The actual final appended map, with its two canonical object transports. -/
theorem append_last_map (A : Obj C rank) {Y : C}
    (q : A.chain.obj (Fin.last A.dim) ⟶ Y) :
    (appendChain A.chain q).map (homOfLE (Fin.le_last (Fin.last A.dim).castSucc)) =
      eqToHom (appendChain_obj_castSucc A.chain q (Fin.last A.dim)) ≫ q ≫
        eqToHom (appendChain_obj_last A.chain q).symm := by
  apply (cancel_mono (eqToHom (appendChain_obj_last A.chain q))).mp
  simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using
    appendChain_last_step A.chain q

/-- Extending a genuine exact face to the actual terminal vertex is again an
exact face. Both the adjacent old maps and the new last map are retained. -/
def Face.append (hi : f.index (Fin.last A.dim) < Fin.last B.dim) :
    Face C rank (append C rank A (f.lastMap C rank) (f.lastRank_lt C rank hi)) B where
  index := f.appendIndex C rank hi
  face := by
    change (f.appendIndex C rank hi).monotone.functor ⋙ B.chain =
      appendChain A.chain (f.lastMap C rank)
    apply ComposableArrows.ext (f.append_obj_eq C rank hi)
    intro i hi'
    have hlast : i < A.dim ∨ i = A.dim := by omega
    rcases hlast with hold | rfl
    · have he : Fin.castSuccFunctor (A.dim + 1) ⋙
          ((f.appendIndex C rank hi).monotone.functor ⋙ B.chain) =
        Fin.castSuccFunctor (A.dim + 1) ⋙ appendChain A.chain (f.lastMap C rank) := by
        change (Fin.castSuccFunctor (A.dim + 1) ⋙
          (f.appendIndex C rank hi).monotone.functor) ⋙ B.chain = _
        rw [f.appendIndex_restriction C rank hi, f.face, append_restriction C rank]
      exact CategoryTheory.Functor.congr_hom he
        (homOfLE (show (⟨i, by omega⟩ : Fin (A.dim + 1)) ≤ ⟨i + 1, by omega⟩ from
          by change i ≤ i + 1; omega))
    · change B.chain.map ((f.appendIndex C rank hi).monotone.functor.map
          (homOfLE (Fin.le_last (Fin.last A.dim).castSucc))) =
        eqToHom (f.append_obj_eq C rank hi (Fin.last A.dim).castSucc) ≫
          (appendChain A.chain (f.lastMap C rank)).map
            (homOfLE (Fin.le_last (Fin.last A.dim).castSucc)) ≫
          eqToHom (f.append_obj_eq C rank hi (Fin.last (A.dim + 1))).symm
      simp only [Face.appendIndex_map_to_last, CategoryTheory.Functor.map_comp,
        eqToHom_map, append_last_map, Face.lastMap, Category.assoc,
        eqToHom_trans_assoc, eqToHom_trans]


end CategoryTheory.RankedChainOrder
