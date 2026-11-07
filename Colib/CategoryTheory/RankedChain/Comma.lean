/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.RankedChain.Append
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# Actual append-or-compress comma objects and their arrows

The original direct-rank condition proves that equal-rank terminal arrows
are equality transports. Closure therefore appends a genuinely new vertex or
retains the entire original chain. The exact mixed face-extension theorem
constructs original comma arrows into every closed target. The fixed target
vertex also maps into every such closed object. No comma contraction or
higher-filling assertion is assumed.

Implementation provenance:
`Quillen/CategoryTheory/RankedChain/Comma.lean`
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

/-- The last-vertex map of an actual face is its original terminal composite. -/
theorem lastVertex_map_face {A B : Obj C rank} (f : Face C rank A B) :
    (lastVertex C rank).map (homOfFace C rank f) = f.lastMap C rank := by
  change SemisimplexResolution.lastMap C (A := ⟨A.dim, A.chain⟩) (B := ⟨B.dim, B.chain⟩)
    ⟨(faceOfHom C rank (homOfFace C rank f)).index,
      (faceOfHom C rank (homOfFace C rank f)).face⟩ = _
  rw [faceOfHom_homOfFace]
  rfl

/-- A terminal-index-preserving face has exactly the canonical equality map
as its last-vertex comparison. -/
theorem Face.lastMap_eqToHom {A B : Obj C rank} (f : Face C rank A B)
    (hf : f.index (Fin.last A.dim) = Fin.last B.dim) :
    f.lastMap C rank = eqToHom ((f.obj_eq C rank (Fin.last A.dim)).symm.trans
      (congrArg B.chain.obj hf)) := by
  dsimp [Face.lastMap]
  rw [show homOfLE (Fin.le_last (f.index (Fin.last A.dim))) = eqToHom hf from
    Subsingleton.elim _ _, eqToHom_map, eqToHom_trans]

/-- The actual old-to-append arrow realizes precisely the prescribed comma
structure arrow, after the original terminal object identification. -/
theorem appendFace_lastMap (A : Obj C rank) {Y : C}
    (q : A.chain.obj (Fin.last A.dim) ⟶ Y)
    (hq : rank (A.chain.obj (Fin.last A.dim)) < rank Y) :
    (lastVertex C rank).map (homOfFace C rank (appendFace C rank A q hq)) ≫
      eqToHom (appendChain_obj_last A.chain q) = q := by
  rw [lastVertex_map_face]
  change (eqToHom _ ≫ (appendChain A.chain q).map
    (homOfLE (Fin.le_last (Fin.last A.dim).castSucc))) ≫ _ = _
  rw [Category.assoc, appendChain_last_step, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]

/-- The terminal vertex has identity last-vertex map into the whole chain. -/
theorem vertexFace_lastMap (A : Obj C rank) :
    (lastVertex C rank).map (homOfFace C rank (vertexFace C rank A (Fin.last A.dim))) =
      𝟙 (A.chain.obj (Fin.last A.dim)) := by
  rw [lastVertex_map_face, Face.lastMap_eqToHom C rank _ rfl]
  rfl

/-- The fixed vertex object in the original costructured comma category. -/
def vertexComma (Y : C) : CostructuredArrow (lastVertex C rank) Y :=
  CostructuredArrow.mk (Y := vertex C rank Y) (𝟙 Y)

/-- An append is a real object of the original comma, with its canonical
terminal equality as structure map. -/
def appendCommaObj {Y : C} (S : CostructuredArrow (lastVertex C rank) Y)
    (hS : rank ((lastVertex C rank).obj S.left) < rank Y) :
    CostructuredArrow (lastVertex C rank) Y :=
  CostructuredArrow.mk (Y := append C rank S.left S.hom hS)
    (eqToHom (appendChain_obj_last S.left.chain S.hom))

/-- The actual old diagram includes in its strict append, with exact comma
commutativity rather than a homotopy-commuting surrogate. -/
def toAppendComma {Y : C} (S : CostructuredArrow (lastVertex C rank) Y)
    (hS : rank ((lastVertex C rank).obj S.left) < rank Y) :
    S ⟶ appendCommaObj C rank S hS :=
  CostructuredArrow.homMk (homOfFace C rank (appendFace C rank S.left S.hom hS))
    (appendFace_lastMap C rank S.left S.hom hS)

/-- A comma object is closed exactly when its terminal arrow is an actual
identity transported along equality of the terminal objects. -/
def IsClosed {Y : C} (S : CostructuredArrow (lastVertex C rank) Y) : Prop :=
  ∃ e : (lastVertex C rank).obj S.left = Y, S.hom = eqToHom e

/-- The actual object operation appends a genuinely new terminal vertex, and
compresses a terminal identity by retaining the entire original chain. -/
def closeObj {Y : C} (S : CostructuredArrow (lastVertex C rank) Y) :
    CostructuredArrow (lastVertex C rank) Y := by
  classical
  exact if hS : rank ((lastVertex C rank).obj S.left) < rank Y
    then appendCommaObj C rank S hS else S

/-- Every object has its actual unit arrow into the append-or-compress object. -/
def toClose {Y : C} (S : CostructuredArrow (lastVertex C rank) Y) :
    S ⟶ closeObj C rank S := by
  classical
  unfold closeObj
  split
  · exact toAppendComma C rank S _
  · exact 𝟙 S

/-- Directness proves closure of the compression branch rather than assuming
that an equal-rank arrow is identity. -/
theorem closeObj_closed (hRank : IsDirectRank C rank) {Y : C}
    (S : CostructuredArrow (lastVertex C rank) Y) : IsClosed C rank (closeObj C rank S) := by
  classical
  unfold closeObj
  split
  · exact ⟨appendChain_obj_last S.left.chain S.hom, rfl⟩
  · exact (hRank S.hom).resolve_left ‹_›

/-- The mixed append/compress case: an original face into a chain already
ending at the target extends over the source append, with full strict face
equality and with its last index equal to the target's actual last index. -/
theorem exists_appendFace_to_closed {A B : Obj C rank} (f : Face C rank A B)
    {Y : C} (e : B.chain.obj (Fin.last B.dim) = Y)
    (q : A.chain.obj (Fin.last A.dim) ⟶ Y)
    (sq : f.lastMap C rank ≫ eqToHom e = q)
    (hq : rank (A.chain.obj (Fin.last A.dim)) < rank Y) :
    ∃ t : Face C rank (append C rank A q hq) B,
      t.index (Fin.last (A.dim + 1)) = Fin.last B.dim := by
  cases e
  have heq : f.lastMap C rank = q := by simpa only [eqToHom_refl, Category.comp_id] using sq
  clear sq
  subst q
  have hi : f.index (Fin.last A.dim) < Fin.last B.dim := by
    apply B.strict.lt_iff_lt.mp
    rw [f.obj_eq C rank (Fin.last A.dim)]
    exact hq
  exact ⟨f.append C rank hi, f.appendIndex_last C rank hi⟩

/-- The strict face extension is an actual arrow in the original comma. -/
theorem exists_appendComma_to_closed {Y : C}
    (S B : CostructuredArrow (lastVertex C rank) Y)
    (hS : rank ((lastVertex C rank).obj S.left) < rank Y)
    (hB : IsClosed C rank B) (f : S ⟶ B) :
    Nonempty (appendCommaObj C rank S hS ⟶ B) := by
  obtain ⟨e, he⟩ := hB
  let a := faceOfHom C rank f.left
  have ha : a.lastMap C rank ≫ eqToHom e = S.hom := by
    rw [← lastVertex_map_face, ← he]
    have hf : homOfFace C rank a = f.left := Subsingleton.elim _ _
    rw [hf]
    exact CostructuredArrow.w f
  obtain ⟨t, ht⟩ := exists_appendFace_to_closed C rank a e S.hom ha hS
  refine ⟨CostructuredArrow.homMk (homOfFace C rank t) ?_⟩
  rw [lastVertex_map_face, Face.lastMap_eqToHom C rank t ht, he]
  change eqToHom _ ≫ eqToHom e = eqToHom (appendChain_obj_last S.left.chain S.hom)
  rw [eqToHom_trans]

/-- Every arrow into a closed target extends to the actual append-or-compress
object, including the mixed case with no target append. -/
theorem exists_close_to_closed {Y : C}
    (S B : CostructuredArrow (lastVertex C rank) Y)
    (hB : IsClosed C rank B) (f : S ⟶ B) : Nonempty (closeObj C rank S ⟶ B) := by
  classical
  unfold closeObj
  split
  · exact exists_appendComma_to_closed C rank S B _ hB f
  · exact ⟨f⟩

/-- A specified actual terminal equality includes the fixed target vertex. -/
def closedVertexFace (A : Obj C rank) {Y : C}
    (e : A.chain.obj (Fin.last A.dim) = Y) : Face C rank (vertex C rank Y) A := by
  cases e
  exact vertexFace C rank A (Fin.last A.dim)

/-- The terminal equality exactly cancels the vertex inclusion's comparison. -/
theorem closedVertexFace_comm (A : Obj C rank) {Y : C}
    (e : A.chain.obj (Fin.last A.dim) = Y) :
    (lastVertex C rank).map (homOfFace C rank (closedVertexFace C rank A e)) ≫ eqToHom e =
      𝟙 Y := by
  cases e
  simp only [closedVertexFace, vertexFace_lastMap, eqToHom_refl]
  change (𝟙 (A.chain.obj (Fin.last A.dim))) ≫ 𝟙 _ = 𝟙 _
  exact Category.id_comp _

/-- The fixed target vertex maps into every closed original comma object. -/
def vertexToClosed {Y : C} (S : CostructuredArrow (lastVertex C rank) Y)
    (hS : IsClosed C rank S) : vertexComma C rank Y ⟶ S := by
  let e := hS.choose
  exact CostructuredArrow.homMk (homOfFace C rank (closedVertexFace C rank S.left e))
    (by rw [hS.choose_spec]; exact closedVertexFace_comm C rank S.left e)

end CategoryTheory.RankedChainOrder
