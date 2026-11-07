module

public import Colib.KTheory.Waldhausen.Fibration.LongExactSequence

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
universe u v

variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) [N.coarse.weq.HasTwoOutOfThreeProperty]
  (he : ExtensionAxiom N.coarse) (D : RowFactorization.JointData N)
  (hs : RowFactorization.SecondEndpointSection N D)

example : Function.Surjective (KMap (changeWeak_exact N) 0) :=
  changeWeak_KMap_zero_surjective N he D hs

example (n : ℕ) :
    let h := canonicalFiberMap_isWeakHomotopyEquivalence_general N he D hs
    (KMap (changeWeak_exact N) (n + 1)).range = (changeWeakConnectingHom N h n).ker ∧
    (changeWeakConnectingHom N h n).range = (KMap (acyclicInclusion_exact N) n).ker ∧
    (KMap (acyclicInclusion_exact N) n).range = (KMap (changeWeak_exact N) n).ker :=
  changeWeak_longExactSequence N he D hs n

-- The connecting map has the original homotopy-fiber boundary after comparison.
example (n : ℕ) (a : N.coarse.K (n + 1)) :
    let h := canonicalFiberMap_isWeakHomotopyEquivalence_general N he D hs
    canonicalFiberKMap N n (changeWeakConnectingHom N h n a) =
      Topology.HomotopyFiber.connectingHom (changeWeakMap N) N.coarse.kBasepoint
        V.kBasepoint (changeWeakMap_basepoint N) n a :=
  canonicalFiberKMap_connecting N
    (canonicalFiberMap_isWeakHomotopyEquivalence_general N he D hs) n a
