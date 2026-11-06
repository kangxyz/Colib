/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.SemisimplexResolution.Append
public import Colib.CategoryTheory.TheoremA.ContractibleComma

/-!
# The actual semisimplex last-vertex resolution

Appending the displayed comma arrow gives genuine natural transformations
from the identity and a constant to one endofunctor. Thus every original
last-vertex comma is contractible. The existing contractible-comma Theorem A
gives an actual homotopy equivalence whose forward map is the original functor
map, with no upgrade from weak equivalence and no omitted degenerate chains.

Implementation provenance:
`Quillen/CategoryTheory/SemisimplexResolution/Contraction.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses and universe parameters are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite
open scoped Topology Simplicial
universe u
namespace CategoryTheory.SemisimplexResolution
open CategoryTheory.ComposableArrows
variable (C : Type u) [SmallCategory C]


/-- Append the displayed comma arrow, retaining every old (possibly degenerate) simplex. -/
def appendObj {d : C} (A : CostructuredArrow (lastVertex C) d) : Obj C :=
  ⟨A.left.dim+1, appendChain A.left.chain A.hom⟩

/-- The object over `d` obtained by appending the displayed arrow from `A`'s last vertex to `d`;
its new last-vertex arrow is the equality transport to `d`. -/
def appendCommaObj {d : C} (A : CostructuredArrow (lastVertex C) d) :
    CostructuredArrow (lastVertex C) d :=
  CostructuredArrow.mk (Y := appendObj C A) (eqToHom (appendChain_obj_last A.left.chain A.hom))

/-- The face between appended chains induced by a morphism over `d`, extending its index embedding
by the new terminal vertex. -/
def appendHom {d : C} {A B : CostructuredArrow (lastVertex C) d} (f : A ⟶ B) :
    appendObj C A ⟶ appendObj C B :=
  ⟨appendIndex f.left.index, append_face f.left A.hom B.hom (CostructuredArrow.w f)⟩

theorem lastMap_eqToHom {A B : Obj C} (f : A ⟶ B)
    (h : f.index (Fin.last A.dim) = Fin.last B.dim) :
    lastMap C f = eqToHom ((congrArg
      (fun T : ComposableArrows C A.dim => T.obj (Fin.last A.dim)) f.face).symm.trans
        (congrArg B.chain.obj h)) := by
  dsimp [lastMap]
  rw [show homOfLE (Fin.le_last (f.index (Fin.last A.dim))) = eqToHom h from
    Subsingleton.elim _ _, eqToHom_map, eqToHom_trans]

/-- The morphism over `d` between appended comma objects induced by `f`. -/
def appendCommaMap {d : C} {A B : CostructuredArrow (lastVertex C) d} (f : A ⟶ B) :
    appendCommaObj C A ⟶ appendCommaObj C B :=
  CostructuredArrow.homMk (appendHom C f) (by
    change lastMap C (appendHom C f) ≫ _ = _
    rw [lastMap_eqToHom C _ (appendIndex_last f.left.index)]
    change eqToHom _ ≫ eqToHom (appendChain_obj_last B.left.chain B.hom) =
      eqToHom (appendChain_obj_last A.left.chain A.hom)
    rw [eqToHom_trans])

theorem appendIndex_id (n : ℕ) :
    appendIndex ((OrderIso.refl (Fin (n+1))).toOrderEmbedding) =
      (OrderIso.refl (Fin (n+2))).toOrderEmbedding := by
  ext i
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp

theorem appendIndex_comp {n m k : ℕ} (a : Fin (n + 1) ↪o Fin (m + 1))
    (b : Fin (m + 1) ↪o Fin (k + 1)) :
    appendIndex (a.trans b) = (appendIndex a).trans (appendIndex b) := by
  ext i
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp

/-- The endofunctor of the last-vertex comma category over `d` that appends each object's displayed
arrow to `d`. -/
def appendComma (d : C) : CostructuredArrow (lastVertex C) d ⥤
    CostructuredArrow (lastVertex C) d where
  obj := appendCommaObj C
  map := appendCommaMap C
  map_id A := by
    apply CostructuredArrow.hom_ext
    exact Hom.ext C (appendIndex_id A.left.dim)
  map_comp f g := by
    apply CostructuredArrow.hom_ext
    exact Hom.ext C (appendIndex_comp f.left.index g.left.index)


/-- The face inclusion of the original chain into its extension by the last-vertex arrow to `d`. -/
def originalToAppendHom {d : C} (A : CostructuredArrow (lastVertex C) d) :
    A.left ⟶ appendObj C A :=
  ⟨Fin.castSuccOrderEmb, appendChain_restrict A.left.chain A.hom⟩

/-- The comma morphism from `A` to its appended extension, induced by the face inclusion of the
original chain. -/
def originalToAppend {d : C} (A : CostructuredArrow (lastVertex C) d) :
    A ⟶ appendCommaObj C A :=
  CostructuredArrow.homMk (originalToAppendHom C A) (by
    change (eqToHom _ ≫ (appendChain A.left.chain A.hom).map
      (homOfLE (Fin.le_last (Fin.last A.left.dim).castSucc))) ≫
        eqToHom (appendChain_obj_last A.left.chain A.hom) = A.hom
    rw [Category.assoc, appendChain_to_last]
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [show homOfLE (Fin.le_last (Fin.last A.left.dim)) = 𝟙 _ from Subsingleton.elim _ _,
      CategoryTheory.Functor.map_id, Category.id_comp])

/-- The natural transformation from the identity of the last-vertex comma category over `d` to the
append endofunctor. -/
def identityToAppend (d : C) : 𝟭 (CostructuredArrow (lastVertex C) d) ⟶ appendComma C d where
  app := originalToAppend C
  naturality {A B} f := by
    apply CostructuredArrow.hom_ext
    apply Hom.ext C
    ext i
    change ((f.left.index i).castSucc : Fin (B.left.dim+2)).val =
      (appendIndex f.left.index i.castSucc).val
    rw [appendIndex_castSucc]

/-- The chain of dimension zero consisting of the single object `d`. -/
def vertexObj (d : C) : Obj C := ⟨0, ComposableArrows.mk₀ d⟩

/-- The last-vertex comma object over `d` given by the singleton chain and the identity arrow of
`d`. -/
def vertexComma (d : C) : CostructuredArrow (lastVertex C) d :=
  CostructuredArrow.mk (Y := vertexObj C d) (𝟙 d)

/-- The order embedding from the singleton ordinal selecting the last vertex of an appended chain
of dimension `n + 1`. -/
def terminalIndex (n : ℕ) : Fin 1 ↪o Fin (n+2) :=
  OrderEmbedding.ofStrictMono (fun _ => Fin.last (n+1)) (by
    intro i j hij
    exact False.elim ((lt_irrefl i) (Subsingleton.elim j i ▸ hij)))

/-- The face from the singleton chain at `d` to `A`'s appended chain that selects its new terminal
vertex. -/
def vertexToAppendHom {d : C} (A : CostructuredArrow (lastVertex C) d) :
    vertexObj C d ⟶ appendObj C A :=
  ⟨terminalIndex A.left.dim, by
    refine CategoryTheory.Functor.ext (fun i => appendChain_obj_last A.left.chain A.hom) ?_
    intro i j f
    have hij : i = j := Subsingleton.elim (α := Fin 1) _ _
    subst j
    rw [Subsingleton.elim f (𝟙 _)]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, eqToHom_trans, eqToHom_refl]⟩

/-- The comma morphism from the singleton object at `d` to `A`'s appended extension, selecting the
new terminal vertex. -/
def vertexToAppend {d : C} (A : CostructuredArrow (lastVertex C) d) :
    vertexComma C d ⟶ appendCommaObj C A :=
  CostructuredArrow.homMk (vertexToAppendHom C A) (by
    change lastMap C (vertexToAppendHom C A) ≫ _ = _
    rw [lastMap_eqToHom C _ rfl]
    change eqToHom _ ≫ eqToHom (appendChain_obj_last A.left.chain A.hom) = 𝟙 d
    simp only [eqToHom_trans, eqToHom_refl])

/-- The natural transformation from the constant singleton-chain functor to the append endofunctor
of the last-vertex comma category over `d`. -/
def constantToAppend (d : C) :
    (CategoryTheory.Functor.const (CostructuredArrow (lastVertex C) d)).obj (vertexComma C d) ⟶
      appendComma C d where
  app := vertexToAppend C
  naturality {A B} f := by
    apply CostructuredArrow.hom_ext
    apply Hom.ext C
    ext i
    change (Fin.last (B.left.dim+1)).val =
      (appendIndex f.left.index (Fin.last (A.left.dim+1))).val
    rw [appendIndex_last]


/-- The actual last-vertex comma is contracted by the append-arrow zigzag. -/
theorem comma_contractible (d : C) :
    ContractibleSpace (ClassifyingSpace (CostructuredArrow (lastVertex C) d)) := by
  apply (contractible_iff_id_nullhomotopic _).2
  refine ⟨classifyingSpacePoint (vertexComma C d), ?_⟩
  have h₁ := classifyingSpaceNaturalTransformationHomotopy (identityToAppend C d)
  have h₂ := classifyingSpaceNaturalTransformationHomotopy (constantToAppend C d)
  simpa only [classifyingSpaceMap_id, TopCat.hom_id, classifyingSpaceMap_const] using
    (ContinuousMap.Homotopic.trans ⟨h₁⟩ ⟨h₂.symm⟩)

/-- All semisimplices, including degenerate chains, give an actual category
resolution with the original last-vertex map as forward map. -/
def lastVertexHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (Obj C)) (ClassifyingSpace C) :=
  TheoremA.contractibleCommaClassifyingHomotopyEquiv (lastVertex C) (comma_contractible C)

@[simp] theorem lastVertexHomotopyEquiv_toFun :
    (lastVertexHomotopyEquiv C).toFun = (classifyingSpaceMap (lastVertex C)).hom :=
  TheoremA.contractibleCommaClassifyingHomotopyEquiv_toFun _ _

end CategoryTheory.SemisimplexResolution
