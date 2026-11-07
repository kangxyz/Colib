import Colib.KTheory.Waldhausen.Iterated.StableFunctoriality
import Colib.KTheory.Waldhausen.Fibration.StableConnectingComparison

noncomputable section

open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.Fibration Topology Topology.LoopPrespectrum
open scoped Topology unitInterval

universe u v

namespace WaldhausenSpectrumFibrationTests

section OriginalGroups

-- The original object and hom universes remain independent; exact functors use the same pair.
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  (W : Structure C) (V : Structure D) (U : Structure E)
  {F G : C ⥤ D} {J : D ⥤ E}
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (hG : IsExact W.cof W.weq V.cof V.weq G)
  (hJ : IsExact V.cof V.weq U.cof U.weq J)

example : LoopPrespectrum.{max u v} := originalPrespectrum W

example : LoopPrespectrum.Homotopy (exactOriginalPrespectrumMap W W (IsExact.id _ _))
    (𝟙 (originalPrespectrum W)) := exactOriginalPrespectrumMapIdHomotopy W

example : LoopPrespectrum.Homotopy (exactOriginalPrespectrumMap W U (hF.comp hJ))
    (exactOriginalPrespectrumMap W V hF ≫ exactOriginalPrespectrumMap V U hJ) :=
  exactOriginalPrespectrumMapCompHomotopy W V U hF hJ

example : originalPrespectrumMap W V (zeroFunctor_isExact W V) rfl =
    LoopPrespectrum.zeroHom (originalPrespectrum W) (originalPrespectrum V) :=
  originalPrespectrumMap_zeroFunctor W V

example : Additive (W.K 0) ≃+ stableHomotopyGroup (originalPrespectrum W) 0 :=
  originalKStableEquiv W 0

example (n : ℕ) (a : Additive (W.K n)) :
    originalKStableEquiv W n a = stableHomotopyι (originalPrespectrum W) (n : ℤ) 0
      (originalKStableStageEquiv W n a) := originalKStableEquiv_apply W n a

-- K0 naturality uses the original public KMap, not a replacement map on generators.
example (a : W.K 0) :
    originalKStableEquiv V 0 (Additive.ofMul (KMap hF 0 a)) =
      exactStableKMap W V hF 0 (originalKStableEquiv W 0 (Additive.ofMul a)) :=
  originalKStableEquiv_exact_naturality W V hF 0 a

example (d : ℤ) : exactStableKMap W W (IsExact.id _ _) d = 𝟙 _ :=
  exactStableKMap_id W d

example (d : ℤ) :
    exactStableKMap W U (hF.comp hJ) d = exactStableKMap W V hF d ≫ exactStableKMap V U hJ d :=
  exactStableKMap_comp W V U hF hJ d

example (η : F ⟶ G) (hη : ∀ A, V.weq (η.app A)) (d : ℤ) :
    exactStableKMap W V hF d = exactStableKMap W V hG d :=
  exactStableKMap_weakNatTrans W V hF hG η hη d

example : IsStableEquivalence (exactOriginalPrespectrumMap W V hF) ↔
    ∀ n : ℕ, Function.Bijective (KMap hF n) :=
  exactOriginalPrespectrumMap_isStableEquivalence_iff W V hF

example (d : ℤ) (hd : d < 0) :
    Subsingleton (stableHomotopyGroup (originalPrespectrum W) d) :=
  originalStableHomotopyGroup_neg_subsingleton W d hd

end OriginalGroups

section ActualFiber

variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V)

example : originalPrespectrum (acyclicStructure N) ⟶
    homotopyFiber (changeWeakPrespectrumMap N) := canonicalFiberPrespectrumMap N

-- The defining lift is exactly the original whole nullhomotopy, including its path coordinate.
example : canonicalFiberPrespectrumMap N =
    homotopyFiberLift (changeWeakPrespectrumMap N) (acyclicInclusionPrespectrumMap N)
      (acyclicPrespectrumNullhomotopy N) := rfl

example (n : ℕ) (x : (originalPrespectrum (acyclicStructure N)).space n)
    (s : unitInterval) :
    ((canonicalFiberPrespectrumMap N).map n x).1.2 s =
      (acyclicPrespectrumNullhomotopy N).level n (s, x) :=
  canonicalFiberPrespectrumMap_path N n x s

example (t : unitInterval) (x : (acyclicStructure N).Delooping) :
    (acyclicPrespectrumNullhomotopy N).level 1
      (t, (acyclicStructure N).asSmallDeloopingHomeomorph x) =
      N.coarse.asSmallDeloopingHomeomorph (acyclicNullhomotopy N (t, x)) :=
  acyclicPrespectrumNullhomotopy_level_one N t x

example : canonicalFiberPrespectrumMap N ≫
    homotopyFiberProjection (changeWeakPrespectrumMap N) = acyclicInclusionPrespectrumMap N :=
  canonicalFiberPrespectrumMap_projection N

example (h : IsWeakHomotopyEquivalence (canonicalFiberMap N)) :
    Function.Surjective ((stableHomotopyFunctor 0).map (changeWeakPrespectrumMap N)) :=
  changeWeakPrespectrumMap_zero_surjective N h

-- Negative one is a consequence of original K0 surjectivity and stable fiber exactness.
example (h : IsWeakHomotopyEquivalence (canonicalFiberMap N)) :
    Subsingleton (stableHomotopyGroup (homotopyFiber (changeWeakPrespectrumMap N)) (-1)) :=
  changeWeakPrespectrumFiber_neg_subsingleton N h (-1) (by omega)

example [N.coarse.weq.HasTwoOutOfThreeProperty]
    (he : ExtensionAxiom N.coarse) (D : RowFactorization.JointData N)
    (hs : RowFactorization.SecondEndpointSection N D) :
    IsStableEquivalence (canonicalFiberPrespectrumMap N) :=
  canonicalFiberPrespectrumMap_isStableEquivalence_general N he D hs

example [N.coarse.weq.HasTwoOutOfThreeProperty]
    (he : ExtensionAxiom N.coarse) (D : RowFactorization.JointData N)
    (hs : RowFactorization.SecondEndpointSection N D) (d : ℤ) :
    IsIso ((stableHomotopyFunctor d).map (canonicalFiberPrespectrumMap N)) :=
  canonicalFiberPrespectrumMap_isStableEquivalence_general N he D hs d

-- The explicit minus and integer degree transport remain present, including K1 to K0.
example (h : IsWeakHomotopyEquivalence (canonicalFiberMap N))
    (κ : ((0 + 1 : ℕ) : ℤ) = (0 : ℤ) + 1) (a : N.coarse.K 1) :
    stableFiberConnecting (changeWeakPrespectrumMap N) (0 : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup (originalPrespectrum N.coarse)) κ)
          (originalKStableEquiv N.coarse 1 (Additive.ofMul a))) =
      -((stableHomotopyFunctor (0 : ℤ)).map (canonicalFiberPrespectrumMap N)
        (originalKStableEquiv (acyclicStructure N) 0
          (Additive.ofMul (changeWeakConnectingHom N h 0 a)))) :=
  originalKStableEquiv_connecting_sign N h 0 κ a

example (h : IsWeakHomotopyEquivalence (canonicalFiberMap N)) (n : ℕ)
    (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1) (a : N.coarse.K (n + 1)) :
    let := acyclicPrespectrumFiberLift_nonneg_isIso N h n
    stableFiberLiftConnecting (acyclicInclusionPrespectrumMap N) (changeWeakPrespectrumMap N)
        (acyclicPrespectrumNullhomotopy N) (n : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup (originalPrespectrum N.coarse)) κ)
          (originalKStableEquiv N.coarse (n + 1) (Additive.ofMul a))) =
      -(originalKStableEquiv (acyclicStructure N) n
        (Additive.ofMul (changeWeakConnectingHom N h n a))) :=
  originalKStableEquiv_liftConnecting_sign N h n κ a

attribute [local instance] Additivity.KCommGroup

example (h : IsWeakHomotopyEquivalence (canonicalFiberMap N)) (n : ℕ)
    (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1) :
    AddCommGrpCat.ofHom (originalKStableEquiv N.coarse (n + 1)).toAddMonoidHom ≫
        eqToHom (congrArg (stableHomotopyGroup (originalPrespectrum N.coarse)) κ) ≫
        stableFiberConnecting (changeWeakPrespectrumMap N) (n : ℤ) =
      -(AddCommGrpCat.ofHom (changeWeakConnectingHom N h n).toAdditive ≫
        AddCommGrpCat.ofHom (originalKStableEquiv (acyclicStructure N) n).toAddMonoidHom ≫
        (stableHomotopyFunctor (n : ℤ)).map (canonicalFiberPrespectrumMap N)) :=
  originalKStableEquiv_connecting_sign_hom N h n κ

end ActualFiber
end WaldhausenSpectrumFibrationTests
