/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Fibration.CanonicalFiberMap
public import Colib.KTheory.Waldhausen.Fibration.GeneralComparison
public import Colib.KTheory.Waldhausen.Connected
public import Colib.Topology.HomotopyFiber.LESTail
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalenceProperty
public import Colib.Topology.Homotopy.HomotopyGroup.ZeroDetection

/-! # The original change-of-weak-equivalences long exact sequence

A weak original canonical fiber comparison transports the actual topological
long exact sequence to the original KMaps. The degree-zero surjectivity uses
the pointed-set tail and connectedness of the acyclic S-realization. Explicit
comparison hypotheses let this algebraic layer apply in both category universes.


Implementation provenance:
`Quillen/Waldhausen/Fibration/LongExactSequence.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps, bounds, hypotheses
and independent object/hom universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology
open CategoryTheory
universe u v
namespace Topology
private theorem weak_homotopy_bijective_based
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : C(X, Y)} (h : IsWeakHomotopyEquivalence f) (x : X) (y : Y)
    (hy : f x = y) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) f hy) := by
  subst y
  exact h.homotopy_bijective x n
end Topology
namespace CategoryTheory.Waldhausen.Fibration
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V)

/-- A weak original comparison gives bijectivity of its original based map. -/
theorem canonicalFiberKMap_bijective_of_weak
    (h : IsWeakHomotopyEquivalence (canonicalFiberMap N)) (n : ℕ) :
    Function.Bijective (canonicalFiberKMap N n) := by
  exact weak_homotopy_bijective_based h _ _ (canonicalFiberMap_basepoint N) (n + 1)

/-- Original acyclic inclusion is precisely the kernel of changing weak classes. -/
theorem range_acyclicInclusion_eq_ker_changeWeak_of_weak
    (h : IsWeakHomotopyEquivalence (canonicalFiberMap N)) (n : ℕ) :
    (KMap (acyclicInclusion_exact N) n).range =
      (KMap (changeWeak_exact N) n).ker := by
  rw [KMap_eq_piMap_of_zeroEq (changeWeak_exact N) N.zero_eq.symm n]
  change (KMap (acyclicInclusion_exact N) n).range =
    (HomotopyGroup.piMap n (changeWeakMap N) (changeWeakMap_basepoint N)).ker
  rw [← HomotopyFiber.piMap_range_projection_eq_ker (changeWeakMap N)
    N.coarse.kBasepoint V.kBasepoint (changeWeakMap_basepoint N) n]
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨canonicalFiberKMap N n a,
      DFunLike.congr_fun (canonicalFiberKMap_projection N n) a⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨b, rfl⟩ := (canonicalFiberKMap_bijective_of_weak N h n).surjective a
    exact ⟨b, (DFunLike.congr_fun (canonicalFiberKMap_projection N n) b).symm⟩

/-- The true connecting homomorphism, transported by the original comparison. -/
def changeWeakConnectingHom
    (h : IsWeakHomotopyEquivalence (canonicalFiberMap N)) (n : ℕ) :
    N.coarse.K (n + 1) →* (acyclicStructure N).K n :=
  (MulEquiv.ofBijective (canonicalFiberKMap N n)
    (canonicalFiberKMap_bijective_of_weak N h n)).symm.toMonoidHom.comp
      (HomotopyFiber.connectingHom (changeWeakMap N) N.coarse.kBasepoint
        V.kBasepoint (changeWeakMap_basepoint N) n)

/-- The transported boundary still has the exact genuine homotopy-fiber boundary. -/
theorem canonicalFiberKMap_connecting
    (h : IsWeakHomotopyEquivalence (canonicalFiberMap N)) (n : ℕ)
    (a : N.coarse.K (n + 1)) :
    canonicalFiberKMap N n (changeWeakConnectingHom N h n a) =
      HomotopyFiber.connectingHom (changeWeakMap N) N.coarse.kBasepoint
        V.kBasepoint (changeWeakMap_basepoint N) n a :=
  (MulEquiv.ofBijective (canonicalFiberKMap N n)
    (canonicalFiberKMap_bijective_of_weak N h n)).apply_symm_apply _

/-- Positive exactness at the original acyclic K-group. -/
theorem range_changeWeakConnectingHom_eq_ker_acyclicInclusion
    (h : IsWeakHomotopyEquivalence (canonicalFiberMap N)) (n : ℕ) :
    (changeWeakConnectingHom N h n).range = (KMap (acyclicInclusion_exact N) n).ker := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    change KMap (acyclicInclusion_exact N) n (changeWeakConnectingHom N h n b) = 1
    rw [← DFunLike.congr_fun (canonicalFiberKMap_projection N n)
      (changeWeakConnectingHom N h n b)]
    change HomotopyGroup.piMap n (HomotopyFiber.projection (changeWeakMap N) N.coarse.kBasepoint)
      (HomotopyFiber.projection_basepoint _ _ V.kBasepoint (changeWeakMap_basepoint N))
      (canonicalFiberKMap N n (changeWeakConnectingHom N h n b)) = 1
    rw [canonicalFiberKMap_connecting]
    have hm : HomotopyFiber.connectingHom (changeWeakMap N) N.coarse.kBasepoint
        V.kBasepoint (changeWeakMap_basepoint N) n b ∈
        (HomotopyFiber.connectingHom (changeWeakMap N) N.coarse.kBasepoint
          V.kBasepoint (changeWeakMap_basepoint N) n).range := ⟨b, rfl⟩
    rw [HomotopyFiber.range_connectingHom_eq_ker_projection] at hm
    exact hm
  · intro ha
    have hm : canonicalFiberKMap N n a ∈
        (HomotopyFiber.connectingHom (changeWeakMap N) N.coarse.kBasepoint
          V.kBasepoint (changeWeakMap_basepoint N) n).range := by
      rw [HomotopyFiber.range_connectingHom_eq_ker_projection]
      exact (DFunLike.congr_fun (canonicalFiberKMap_projection N n) a).trans ha
    obtain ⟨b, hb⟩ := hm
    refine ⟨b, (canonicalFiberKMap_bijective_of_weak N h n).injective ?_⟩
    exact (canonicalFiberKMap_connecting N h n b).trans hb

/-- Positive exactness at the original coarse K-group. -/
theorem range_changeWeak_eq_ker_changeWeakConnectingHom
    (h : IsWeakHomotopyEquivalence (canonicalFiberMap N)) (n : ℕ) :
    (KMap (changeWeak_exact N) (n + 1)).range = (changeWeakConnectingHom N h n).ker := by
  rw [KMap_eq_piMap_of_zeroEq (changeWeak_exact N) N.zero_eq.symm (n + 1)]
  change (HomotopyGroup.piMap (n + 1) (changeWeakMap N) (changeWeakMap_basepoint N)).range = _
  rw [HomotopyFiber.range_piMap_eq_ker_connectingHom]
  ext a
  constructor
  · intro ha
    apply (canonicalFiberKMap_bijective_of_weak N h n).injective
    exact (canonicalFiberKMap_connecting N h n a).trans (ha.trans (map_one _).symm)
  · intro ha
    change changeWeakConnectingHom N h n a = 1 at ha
    change HomotopyFiber.connectingHom (changeWeakMap N) N.coarse.kBasepoint
      V.kBasepoint (changeWeakMap_basepoint N) n a = 1
    rw [← canonicalFiberKMap_connecting N h n a, ha, map_one]

/-- Every recurring position of the original K-theory long exact sequence. -/
theorem changeWeak_positiveLongExactSequence_of_weak
    (h : IsWeakHomotopyEquivalence (canonicalFiberMap N)) (n : ℕ) :
    (KMap (changeWeak_exact N) (n + 1)).range = (changeWeakConnectingHom N h n).ker ∧
    (changeWeakConnectingHom N h n).range = (KMap (acyclicInclusion_exact N) n).ker ∧
    (KMap (acyclicInclusion_exact N) n).range = (KMap (changeWeak_exact N) n).ker :=
  ⟨range_changeWeak_eq_ker_changeWeakConnectingHom N h n,
    range_changeWeakConnectingHom_eq_ker_acyclicInclusion N h n,
    range_acyclicInclusion_eq_ker_changeWeak_of_weak N h n⟩

/-- If the original acyclic inclusion is injective, the true boundary vanishes. -/
theorem connectingHom_eq_one_of_acyclicInclusion_injective
    (h : IsWeakHomotopyEquivalence (canonicalFiberMap N)) (n : ℕ)
    (hi : Function.Injective (KMap (acyclicInclusion_exact N) n))
    (a : N.coarse.K (n + 1)) :
    HomotopyFiber.connectingHom (changeWeakMap N) N.coarse.kBasepoint
      V.kBasepoint (changeWeakMap_basepoint N) n a = 1 := by
  let c := HomotopyFiber.connectingHom (changeWeakMap N) N.coarse.kBasepoint
    V.kBasepoint (changeWeakMap_basepoint N) n a
  obtain ⟨b, hb⟩ := (canonicalFiberKMap_bijective_of_weak N h n).surjective c
  have hz : KMap (acyclicInclusion_exact N) n b = 1 := by
    rw [← DFunLike.congr_fun (canonicalFiberKMap_projection N n) b]
    change HomotopyGroup.piMap n (HomotopyFiber.projection (changeWeakMap N) N.coarse.kBasepoint)
      (HomotopyFiber.projection_basepoint _ _ V.kBasepoint (changeWeakMap_basepoint N))
      (canonicalFiberKMap N n b) = 1
    rw [hb]
    have hm : c ∈ (HomotopyFiber.connectingHom (changeWeakMap N) N.coarse.kBasepoint
        V.kBasepoint (changeWeakMap_basepoint N) n).range := ⟨a, rfl⟩
    rw [HomotopyFiber.range_connectingHom_eq_ker_projection] at hm
    exact hm
  have hb1 : b = 1 := hi (hz.trans (map_one _).symm)
  exact hb.symm.trans (by rw [hb1, map_one])

/-- Positive K-degree surjectivity uses exactness and the actual injective inclusion. -/
theorem changeWeak_KMap_succ_surjective_of_weak
    (h : IsWeakHomotopyEquivalence (canonicalFiberMap N)) (n : ℕ)
    (hi : Function.Injective (KMap (acyclicInclusion_exact N) n)) :
    Function.Surjective (KMap (changeWeak_exact N) (n + 1)) := by
  rw [KMap_eq_piMap_of_zeroEq (changeWeak_exact N) N.zero_eq.symm (n + 1)]
  intro a
  have hm : a ∈ (HomotopyFiber.connectingHom (changeWeakMap N) N.coarse.kBasepoint
      V.kBasepoint (changeWeakMap_basepoint N) n).ker :=
    connectingHom_eq_one_of_acyclicInclusion_injective N h n hi a
  rw [← HomotopyFiber.range_piMap_eq_ker_connectingHom] at hm
  exact hm

/-- Degree zero uses the actual pointed-set tail and connected acyclic S-space. -/
theorem changeWeak_KMap_zero_surjective_of_weak
    (h : IsWeakHomotopyEquivalence (canonicalFiberMap N)) :
    Function.Surjective (KMap (changeWeak_exact N) 0) := by
  rw [KMap_eq_piMap_of_zeroEq (changeWeak_exact N) N.zero_eq.symm 0]
  have hh := weak_homotopy_bijective_based h _ _ (canonicalFiberMap_basepoint N) 0
  let := subsingleton_homotopyGroup_zero (acyclicStructure N).kBasepoint
  let : Subsingleton (HomotopyGroup.Pi 0
      (HomotopyFiber (changeWeakMap N) N.coarse.kBasepoint)
      (HomotopyFiber.basepoint (changeWeakMap N) N.coarse.kBasepoint
        V.kBasepoint (changeWeakMap_basepoint N))) := hh.surjective.subsingleton
  intro a
  exact (HomotopyFiber.mem_range_piMap_iff_connectingMap_constant (changeWeakMap N)
    N.coarse.kBasepoint V.kBasepoint (changeWeakMap_basepoint N) 0 a).2
      (Subsingleton.elim _ _)

/-- All K-degrees, with the zero case separated rather than discarded. -/
theorem changeWeak_KMap_surjective_of_weak
    (h : IsWeakHomotopyEquivalence (canonicalFiberMap N))
    (hi : ∀ n, Function.Injective (KMap (acyclicInclusion_exact N) n)) (n : ℕ) :
    Function.Surjective (KMap (changeWeak_exact N) n) := by
  cases n with
  | zero => exact changeWeak_KMap_zero_surjective_of_weak N h
  | succ n => exact changeWeak_KMap_succ_surjective_of_weak N h n (hi n)
end CategoryTheory.Waldhausen.Fibration

namespace CategoryTheory.Waldhausen.Fibration

variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) [N.coarse.weq.HasTwoOutOfThreeProperty]
  (he : ExtensionAxiom N.coarse) (D : RowFactorization.JointData N)
  (hs : RowFactorization.SecondEndpointSection N D)

/-- The proved structural fibration theorem supplies the original long exact
sequence, with its actual transported homotopy-fiber boundary. -/
@[colib_tag "COL-0259",
  colib_ref "WeibelKBook" "V, Theorem 2.1, pp. 12-13" "adaptation"
    "Actual change-of-weak KMaps and path-space boundary under structural cylinder assumptions"]
theorem changeWeak_longExactSequence (n : ℕ) :
    let h := canonicalFiberMap_isWeakHomotopyEquivalence_general N he D hs
    (KMap (changeWeak_exact N) (n + 1)).range = (changeWeakConnectingHom N h n).ker ∧
    (changeWeakConnectingHom N h n).range = (KMap (acyclicInclusion_exact N) n).ker ∧
    (KMap (acyclicInclusion_exact N) n).range = (KMap (changeWeak_exact N) n).ker :=
  changeWeak_positiveLongExactSequence_of_weak N
    (canonicalFiberMap_isWeakHomotopyEquivalence_general N he D hs) n

include he D hs in
/-- The original change-of-weak map is onto in K-zero, using the pointed-set tail
of the proved fibration rather than dropping the bottom degree. -/
@[colib_tag "COL-0259"]
theorem changeWeak_KMap_zero_surjective :
    Function.Surjective (KMap (changeWeak_exact N) 0) :=
  changeWeak_KMap_zero_surjective_of_weak N
    (canonicalFiberMap_isWeakHomotopyEquivalence_general N he D hs)

end CategoryTheory.Waldhausen.Fibration
