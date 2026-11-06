module

public import Colib.KTheory.Waldhausen.GilletWaldhausen.GeneralComparison

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.GilletWaldhausen CochainComplex
open Topology
universe u v
attribute [local instance] Abelian.hasFiniteBiproducts

variable {A : Type (max u v)} [Category.{v} A] [Abelian A]
  (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]

-- The actual bounded-complex fiber theorem does not need kernel closure.
example : IsWeakHomotopyEquivalence (Fibration.canonicalFiberMap (boundedTermsNested P)) :=
  boundedTerms_canonicalFiberMap_isWeakHomotopyEquivalence_general P

variable [(abelianExactStructure A).IsKernelClosed P]
local instance : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P

-- The final theorem includes degree zero without any fiber or comparison premise.
example : Function.Bijective (KMap (boundedTermsSingle_coarseExact P 0) 0) :=
  boundedTermsSingle_coarse_KMap_bijective_general P 0

example (n : ℕ) : Function.Bijective (KMap (boundedTermsSingle_coarseExact P 0) n) :=
  boundedTermsSingle_coarse_KMap_bijective_general P n

-- The forward homomorphism is definitionally the original normalized KMap.
example (n : ℕ) : (boundedTermsSingleCoarseKEquivGeneral P n).toMonoidHom =
    KMap (boundedTermsSingle_coarseExact P 0) n := rfl

example (n : ℕ)
    (x : (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K n) :
    boundedTermsSingleCoarseKEquivGeneral P n x =
      KMap (boundedTermsSingle_coarseExact P 0) n x := rfl

-- The fine/coarse triangle retains the same single insertion and change-of-weak map.
example (n : ℕ) : KMap (boundedTermsSingle_coarseExact P 0) n =
    (KMap (Fibration.changeWeak_exact (boundedTermsNested P)) n).comp
      (KMap (boundedTermsSingleExactFunctor P 0).waldhausenExact n) :=
  boundedTermsSingle_coarse_KMap P 0 n
