import Colib.CategoryTheory.Waldhausen.SMap
import Colib.CategoryTheory.Waldhausen.ExactFunctorIso
import Colib.CategoryTheory.Waldhausen.CofibrationClosedSubcategory
import Colib.CategoryTheory.Waldhausen.EquivalenceStructure

open CategoryTheory

#check Waldhausen.Structure
#check Waldhausen.IsExact.comp
#check Waldhausen.IsExact.of_iso
#check Waldhausen.sSetMap_id
#check Waldhausen.sSetMap_comp
#check Waldhausen.CofibrationClosedSubcategory.inclusion_exact
#check Waldhausen.Structure.ofEquivalence_inverse_exact
#print axioms Waldhausen.sSetMap_comp
#print axioms Waldhausen.CofibrationClosedSubcategory.inclusion_exact

open CategoryTheory.Limits

universe u v
namespace WaldhausenFoundationTests

variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  {cof weq : MorphismProperty C} {cof' weq' : MorphismProperty D}
  {cof'' weq'' : MorphismProperty E} {F : C ⥤ D} {G : D ⥤ E}
  (hF : Waldhausen.IsExact cof weq cof' weq' F)
  (hG : Waldhausen.IsExact cof' weq' cof'' weq'' G)

example (n : SimplexCategoryᵒᵖ) (A : (Waldhausen.sSet cof weq).obj n) :
    ((Waldhausen.sSetMap hF).app n A).val = A.val ⋙ F := rfl

example : Waldhausen.sSetMap (hF.comp hG) =
    Waldhausen.sSetMap hF ≫ Waldhausen.sSetMap hG :=
  Waldhausen.sSetMap_comp hF hG

example (W : Waldhausen.Structure C) :
    Waldhausen.sSetMap (Waldhausen.IsExact.id W.cof W.weq) =
      𝟙 (Waldhausen.sSet W.cof W.weq) := Waldhausen.sSetMap_id W

example (W : Waldhausen.Structure C) (P : ObjectProperty C)
    (H : Waldhausen.CofibrationClosedSubcategory.Closed W P) :
    Waldhausen.IsExact
      (Waldhausen.CofibrationClosedSubcategory.waldhausenStructure W P H).cof
      (Waldhausen.CofibrationClosedSubcategory.waldhausenStructure W P H).weq
      W.cof W.weq P.ι :=
  Waldhausen.CofibrationClosedSubcategory.inclusion_exact W P H

end WaldhausenFoundationTests
