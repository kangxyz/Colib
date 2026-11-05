import Colib.CategoryTheory.Waldhausen.SMap
import Colib.CategoryTheory.Waldhausen.ExactFunctorIso
import Colib.CategoryTheory.Waldhausen.CofibrationClosedSubcategory
import Colib.CategoryTheory.Waldhausen.EquivalenceStructure

/-! Downstream regressions for the actual categorical Waldhausen models.
No abstract replacement simplicial object or extra exactness axiom is used. -/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v u' v'

namespace WaldhausenRegression
open CategoryTheory.Waldhausen

section SimplicialObject
variable {C : Type u} [Category.{v} C] (cof weq : MorphismProperty C)

/-- The actual n-simplices are the original quotient-diagram functors. -/
theorem simplex_object (n : SimplexCategory) :
    (sSet cof weq).obj (op n) = { A : Grid n ⥤ C // IsSimplex cof weq A } := rfl

/-- The full simplex predicate, not only its object set, survives reindexing. -/
theorem reindex_isSimplex {m n : SimplexCategory} (α : m ⟶ n)
    (A : (sSet cof weq).obj (op n)) :
    IsSimplex cof weq (gridMap α ⋙ A.val) := A.property.precomp cof weq α

/-- Face maps are simultaneous reindexing in both actual grid directions. -/
theorem face_value {n : ℕ} (i : Fin (n + 2))
    (A : (sSet cof weq).obj (op ⦋n + 1⦌)) :
    ((sSet cof weq).map (SimplexCategory.δ i).op A).val =
      gridMap (SimplexCategory.δ i) ⋙ A.val := rfl

/-- Degeneracy maps retain the same quotient-diagram model. -/
theorem degeneracy_value {n : ℕ} (i : Fin (n + 1))
    (A : (sSet cof weq).obj (op ⦋n⦌)) :
    ((sSet cof weq).map (SimplexCategory.σ i).op A).val =
      gridMap (SimplexCategory.σ i) ⋙ A.val := rfl

/-- Reindexing obeys the actual contravariant composition law. -/
theorem reindex_comp {l m n : SimplexCategory} (α : l ⟶ m) (β : m ⟶ n)
    (A : (sSet cof weq).obj (op n)) :
    (sSet cof weq).map (α ≫ β).op A =
      (sSet cof weq).map α.op ((sSet cof weq).map β.op A) := rfl

/-- Every original simplex retains its zero diagonal without a chosen-zero equality. -/
theorem diagonal_zero {n : SimplexCategory} (A : (sSet cof weq).obj (op n))
    (t i : Fin (n.len + 1)) : IsZero (A.val.obj (grid t i i le_rfl)) :=
  A.property.zero t i

/-- The nerve direction retains weak equivalences, not arbitrary morphisms. -/
theorem nerve_weak {n : SimplexCategory} (A : (sSet cof weq).obj (op n))
    (s t i j : Fin (n.len + 1)) (hst : s ≤ t) (hij : i ≤ j) :
    weq (A.val.map (homOfLE (show grid s i j hij ≤ grid t i j hij from
      ⟨hst, le_rfl, le_rfl⟩))) := A.property.weak s t i j hst hij

end SimplicialObject

section FunctorMaps
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  {cof weq : MorphismProperty C} {cof' weq' : MorphismProperty D}
  {cof'' weq'' : MorphismProperty E} {F : C ⥤ D} {G : D ⥤ E}
  (hF : IsExact cof weq cof' weq' F) (hG : IsExact cof' weq' cof'' weq'' G)

theorem map_value (n : SimplexCategoryᵒᵖ) (A : (sSet cof weq).obj n) :
    ((sSetMap hF).app n A).val = A.val ⋙ F := rfl

theorem map_identity (W : Structure C) :
    sSetMap (IsExact.id W.cof W.weq) = 𝟙 (sSet W.cof W.weq) := sSetMap_id W

theorem map_composition :
    sSetMap (hF.comp hG) = sSetMap hF ≫ sSetMap hG := sSetMap_comp hF hG

theorem map_reindex {m n : SimplexCategory} (α : m ⟶ n)
    (A : (sSet cof weq).obj (op n)) :
    (sSetMap hF).app (op m) ((sSet cof weq).map α.op A) =
      (sSet cof' weq').map α.op ((sSetMap hF).app (op n) A) := rfl

end FunctorMaps

section EquivalenceTransport
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (W : Structure D) (e : C ≌ D) (z : C) (hz : IsZero (e.functor.obj z))

theorem transported_zero : (W.ofEquivalence e z hz).zero = z := rfl

theorem transported_cof :
    (W.ofEquivalence e z hz).cof = W.cof.inverseImage e.functor := rfl

theorem transported_weq :
    (W.ofEquivalence e z hz).weq = W.weq.inverseImage e.functor := rfl

theorem forward_exact :
    IsExact (W.ofEquivalence e z hz).cof (W.ofEquivalence e z hz).weq
      W.cof W.weq e.functor := W.ofEquivalence_exact e z hz

theorem inverse_exact :
    IsExact W.cof W.weq (W.ofEquivalence e z hz).cof (W.ofEquivalence e z hz).weq
      e.inverse := W.ofEquivalence_inverse_exact e z hz

end EquivalenceTransport

section FullSubcategory
open CofibrationClosedSubcategory
variable {C : Type u} [Category.{v} C] (W : Structure C) (P : ObjectProperty C)
    (H : Closed W P)

theorem inclusion_zero : (waldhausenStructure W P H).zero.obj = W.zero := rfl

theorem inclusion_cof :
    (waldhausenStructure W P H).cof = W.cof.inverseImage P.ι := rfl

theorem inclusion_weq :
    (waldhausenStructure W P H).weq = W.weq.inverseImage P.ι := rfl

theorem full_inclusion_exact :
    IsExact (waldhausenStructure W P H).cof (waldhausenStructure W P H).weq
      W.cof W.weq P.ι := inclusion_exact W P H

include H in
/-- Arbitrary chosen subcategory pushouts are actual ambient pushouts. -/
theorem ambient_pushout {A B D Q : P.FullSubcategory}
    {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ Q} {j : D ⟶ Q}
    (hi : W.cof i.hom) (h : IsPushout i f g j) :
    IsPushout i.hom f.hom g.hom j.hom := inclusion_map_pushout W P H hi h

theorem inherited_twoOutOfThree [W.weq.HasTwoOutOfThreeProperty] :
    (waldhausenStructure W P H).weq.HasTwoOutOfThreeProperty := inferInstance

end FullSubcategory
end WaldhausenRegression
