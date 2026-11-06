module
import Colib.KTheory.Quillen.Resolution.LengthOneK
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.ExactCategory.Resolution
universe u
variable {C : Type u} [SmallCategory C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (P : ObjectProperty C)
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [E.IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts] [E.IsKernelClosed P]
example (h : ∀ X, E.ResolutionLength P 1 X) (n : ℕ) :
    (ExactSubcategory.exactStructure E P).K n ≃* E.K n := KEquivOfLengthOne E P h n
example (h : ∀ X, E.ResolutionLength P 1 X) :
    Function.Bijective (inclusionKMap E P 0) := inclusionKMap_bijective_of_length_one E P h 0
example (h : ∀ X, E.ResolutionLength P 1 X) (n : ℕ) :
    (↑(KEquivOfLengthOne E P h n) : (ExactSubcategory.exactStructure E P).K n →* E.K n) =
      (exactInclusion E P).KMap n := KEquivOfLengthOne_coe E P h n
example : (classifyingSpaceMap (exactInclusion E P).normalizedQ).hom
    (ExactSubcategory.exactStructure E P).kBasepoint = E.kBasepoint :=
  (exactInclusion E P).normalizedQ_map_point
