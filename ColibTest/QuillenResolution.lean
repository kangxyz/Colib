module
import Colib.KTheory.Quillen.Resolution.Theorem
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.ExactCategory.Resolution
universe u
variable {C : Type u} [SmallCategory C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (P : ObjectProperty C)
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [E.IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts] [E.IsKernelClosed P]

example (h : E.ResolutionHypothesis P) (n : ℕ) :
    (ExactSubcategory.exactStructure E P).K n ≃* E.K n := KEquiv E P h n
example (h : E.ResolutionHypothesis P) :
    Function.Bijective ((exactInclusion E P).KMap 0) := inclusionKMap_bijective E P h 0
example (h : E.ResolutionHypothesis P) (n : ℕ) :
    (↑(KEquiv E P h n) : (ExactSubcategory.exactStructure E P).K n →* E.K n) =
      (exactInclusion E P).KMap n := KEquiv_coe E P h n
example (h : E.ResolutionHypothesis P) :
    (classifyingHomotopyEquiv E P h).toFun =
      (classifyingSpaceMap (exactInclusion E P).mapQ).hom :=
  classifyingHomotopyEquiv_toFun E P h
example (N : ℕ) (h : ∀ X, E.ResolutionLength P N X) (n : ℕ) :
    (ExactSubcategory.exactStructure E P).K n ≃* E.K n := KEquivOfBounded E P N h n

variable [Fact (E.ResolutionHypothesis P)]
example {m n : ℕ} (h : m ≤ n) : Mono (nerveMap (stratumTransition E P h).mapQ) :=
  stratumTransition_nerveMap_mono E P h
example : IsColimit (nerveFunctor.mapCocone (stratumQCocone E P)) :=
  stratumNerveCoconeIsColimit E P
example : IsColimit (stratumNerveSequenceCocone E P) := stratumNerveSequenceIsColimit E P
example (n : ℕ) : (stratumTransitionHomotopyEquiv E P (Nat.zero_le n)).toFun =
    (classifyingSpaceMap (stratumTransition E P (Nat.zero_le n)).mapQ).hom :=
  stratumTransitionHomotopyEquiv_toFun E P (Nat.zero_le n)
example : (stratumZeroToAmbientHomotopyEquiv E P).toFun =
    (classifyingSpaceMap (exactInclusion E (E.ResolutionLength P 0)).mapQ).hom :=
  stratumZeroToAmbientHomotopyEquiv_toFun E P
