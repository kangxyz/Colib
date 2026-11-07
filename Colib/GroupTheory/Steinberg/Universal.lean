/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.GroupTheory.Steinberg.Matrix
public import Colib.Util.References

/-!
# Universal lifting for the actual stable Steinberg presentation

For a surjective homomorphism `p : H →* StableGeneralLinear.elementary F` whose kernel
is central, `liftToCentralExtension` constructs a homomorphism from the original
finite-rank-labelled Steinberg presentation to `H`, over the original `toElementary`.
`existsUnique_lift_toElementary` proves its uniqueness. The field is arbitrary,
including fields of order two or three, and `H` has an independent universe.

The construction uses commutators of arbitrary preimages of elementary roots.
Centrality makes commutators independent of the selected preimages. Adjoining a
fresh coordinate first proves that all preimages of noninteracting roots commute.
A Hall-Witt identity then proves independence of the intermediate coordinate and
the chain relation. Root addition follows from the commutator product identity.

The private natural-index notation denotes generators of the existing presentation:
`natRoot_eq` proves equality with every actual finite-rank representative. Thus the
construction respects the actual stabilization relators and descends that same
`PresentedGroup`. Perfectness is used for uniqueness, after existence is proved.
Combined with the centrality theorem in `Colib.GroupTheory.Steinberg.Centrality`, these results
give the universal central-extension property of the actual map `toElementary`.
No comparison with a Milnor-symbol presentation or Quillen K2 is used.

## Implementation provenance

Adapted from `Quillen/Algebra/Group/StableSteinbergUniversal.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original generator lift.
-/
@[expose] public section

open scoped commutatorElement
universe u v w
noncomputable section
namespace StableSteinberg
section General

variable {A : Type u} {B : Type v} [_root_.Group A] [_root_.Group B]
variable (p : A →* B) (hc : p.ker ≤ Subgroup.center A)
include hc

private lemma commutator_congr_left {a a' b : A} (ha : p a = p a') :
    ⁅a, b⁆ = ⁅a', b⁆ := by
  have hz : a * a'⁻¹ ∈ Subgroup.center A := hc (by simp [MonoidHom.mem_ker, ha])
  have hzb : Commute (a * a'⁻¹) b :=
    (Subgroup.mem_center_iff.mp hz b).symm
  have hzc : Commute (a * a'⁻¹) ⁅a', b⁆ :=
    (Subgroup.mem_center_iff.mp hz ⁅a', b⁆).symm
  calc
    ⁅a, b⁆ = ⁅(a * a'⁻¹) * a', b⁆ := by simp
    _ = ⁅a', b⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul, hzb.commutator_eq,
        mul_one, hzc.eq, mul_inv_cancel_right]

private lemma commutator_congr {a a' b b' : A} (ha : p a = p a') (hb : p b = p b') :
    ⁅a, b⁆ = ⁅a', b'⁆ := by
  rw [commutator_congr_left p hc ha]
  have h := congrArg Inv.inv (commutator_congr_left p hc (b := a') hb)
  simpa using h

private lemma commutator_commutes {a b c : A}
    (ha : Commute (p a) (p c)) (hb : Commute (p b) (p c)) :
    Commute ⁅a, b⁆ c := by
  have h : c * ⁅a, b⁆ * c⁻¹ = ⁅a, b⁆ := by
    rw [conjugate_commutatorElement]
    apply commutator_congr p hc
    · simp only [map_mul, map_inv]
      rw [ha.symm.eq, mul_inv_cancel_right]
    · simp only [map_mul, map_inv]
      rw [hb.symm.eq, mul_inv_cancel_right]
  exact ((mul_inv_eq_iff_eq_mul).mp h).symm

omit hc in
private lemma commutator_assoc {a b c : A} (hac : Commute a c)
    (hde : Commute ⁅a, b⁆ ⁅b, c⁆) (hec : Commute ⁅b, c⁆ c) :
    ⁅⁅a, b⁆, c⁆ = ⁅a, ⁅b, c⁆⁆ := by
  have hed : Commute ⁅b, c⁆ ⁅⁅a, b⁆, c⁆ := by
    unfold commutatorElement
    exact ((hde.symm.mul_right hec).mul_right hde.symm.inv_right).mul_right hec.inv_right
  have hbc : b * c * b⁻¹ = ⁅b, c⁆ * c := by simp [commutatorElement_def, mul_assoc]
  have h := commutatorElement_commutatorElement_conj_mul a b c
  rw [hac.symm.commutator_eq, commutatorElement_one_left, mul_one,
    hac.symm.eq, mul_inv_cancel_right, hbc,
    commutatorElement_mul_right_eq_mul_conj, hde.commutator_eq, one_mul,
    hed.eq, mul_inv_cancel_right, mul_eq_one_iff_eq_inv, commutatorElement_inv] at h
  exact h

include hc in
private lemma hom_ext_of_perfect {S : Type w} [_root_.Group S] [_root_.Group.IsPerfect S]
    (f g : S →* A) (h : p.comp f = p.comp g) : f = g := by
  have hcomm : commutator S ≤ f.eqLocus g := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    change f ⁅a, b⁆ = g ⁅a, b⁆
    rw [map_commutatorElement, map_commutatorElement]
    exact commutator_congr p hc (congrArg (fun k : S →* B => k a) h)
      (congrArg (fun k : S →* B => k b) h)
  have htop : (⊤ : Subgroup S) ≤ f.eqLocus g := by simpa using hcomm
  ext a
  exact htop trivial

end General

section Roots

variable (F : Type u) [Field F]

/-- Iterated use of the defining one-coordinate stabilization relator. -/
private lemma x_castLE {n m : ℕ} (hnm : n ≤ m) (i j : Fin n) (hij : i ≠ j) (a : F) :
    x F n i j hij a = x F m (i.castLE hnm) (j.castLE hnm)
      (by intro h; exact hij (Fin.ext (congrArg (fun z : Fin m => z.val) h))) a := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m h ih =>
    calc
      _ = x F m (i.castLE h) (j.castLE h) _ a := ih
      _ = _ := by simpa using x_stabilize F m (i.castLE h) (j.castLE h) _ a

/-- A notation for an existing finite-rank generator, with no second presentation. -/
private def natRoot (i j : ℕ) (hij : i ≠ j) (a : F) : Group F :=
  x F (max i j + 1) ⟨i, by omega⟩ ⟨j, by omega⟩ (by simpa using hij) a

private lemma natRoot_eq (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : F) :
    natRoot F i j (by simpa only [ne_eq, Fin.ext_iff] using hij) a = x F n i j hij a := by
  unfold natRoot
  have h : max i.val j.val + 1 ≤ n := by omega
  simpa using x_castLE F h ⟨i, by omega⟩ ⟨j, by omega⟩
    (by intro h'; exact hij (Fin.ext (congrArg (fun z : Fin (max i.val j.val + 1) => z.val) h'))) a

private lemma natRoot_add (i j : ℕ) (hij : i ≠ j) (a b : F) :
    natRoot F i j hij a * natRoot F i j hij b = natRoot F i j hij (a + b) :=
  x_add F _ _ _ _ _ _

private lemma natRoot_commute (i j k l : ℕ) (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i) (a b : F) :
    Commute (natRoot F i j hij a) (natRoot F k l hkl b) := by
  let n := i + j + k + l + 1
  let ii : Fin n := ⟨i, by dsimp [n]; omega⟩
  let jj : Fin n := ⟨j, by dsimp [n]; omega⟩
  let kk : Fin n := ⟨k, by dsimp [n]; omega⟩
  let ll : Fin n := ⟨l, by dsimp [n]; omega⟩
  have hij' : ii ≠ jj := by simpa [ii, jj] using hij
  have hkl' : kk ≠ ll := by simpa [kk, ll] using hkl
  have hjk' : jj ≠ kk := by simpa [jj, kk] using hjk
  have hli' : ll ≠ ii := by simpa [ll, ii] using hli
  simpa only [← natRoot_eq] using x_commute F n ii jj kk ll hij' hkl' hjk' hli' a b

private lemma natRoot_chain (i j k : ℕ) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a b : F) :
    ⁅natRoot F i j hij a, natRoot F j k hjk b⁆ = natRoot F i k hik (a * b) := by
  let n := i + j + k + 1
  let ii : Fin n := ⟨i, by dsimp [n]; omega⟩
  let jj : Fin n := ⟨j, by dsimp [n]; omega⟩
  let kk : Fin n := ⟨k, by dsimp [n]; omega⟩
  have hij' : ii ≠ jj := by simpa [ii, jj] using hij
  have hjk' : jj ≠ kk := by simpa [jj, kk] using hjk
  have hik' : ii ≠ kk := by simpa [ii, kk] using hik
  simpa only [← natRoot_eq] using x_commutator F n ii jj kk hij' hjk' hik' a b

private def rootImage (i j : ℕ) (hij : i ≠ j) (a : F) :
    StableGeneralLinear.elementary F := toElementary F (natRoot F i j hij a)

private lemma rootImage_add (i j : ℕ) (hij : i ≠ j) (a b : F) :
    rootImage F i j hij a * rootImage F i j hij b = rootImage F i j hij (a + b) := by
  simp only [rootImage, ← map_mul, natRoot_add]

private lemma rootImage_commute (i j k l : ℕ) (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i) (a b : F) :
    Commute (rootImage F i j hij a) (rootImage F k l hkl b) :=
  (natRoot_commute F i j k l hij hkl hjk hli a b).map (toElementary F)

private lemma rootImage_chain (i j k : ℕ) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a b : F) :
    ⁅rootImage F i j hij a, rootImage F j k hjk b⁆ = rootImage F i k hik (a * b) := by
  simp only [rootImage, ← map_commutatorElement]
  rw [natRoot_chain F i j k hij hjk hik]

variable {H : Type v} [_root_.Group H]
variable (p : H →* StableGeneralLinear.elementary F) (hp : Function.Surjective p)
variable (hc : p.ker ≤ Subgroup.center H)

private def rootPreimage (i j : ℕ) (hij : i ≠ j) (a : F) : H :=
  (hp (rootImage F i j hij a)).choose

private lemma rootPreimage_map (i j : ℕ) (hij : i ≠ j) (a : F) :
    p (rootPreimage F p hp i j hij a) = rootImage F i j hij a :=
  (hp (rootImage F i j hij a)).choose_spec

include hp hc in
/-- A fresh-coordinate decomposition forces arbitrary preimages of disjoint roots to commute. -/
private lemma preimages_commute (i j k l : ℕ) (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i) (a b : F) {u v : H}
    (hu : p u = rootImage F i j hij a) (hv : p v = rootImage F k l hkl b) :
    Commute u v := by
  let t := i + j + k + l + 1
  have hit : i ≠ t := by dsimp [t]; omega
  have htj : t ≠ j := by dsimp [t]; omega
  have htk : t ≠ k := by dsimp [t]; omega
  have hlt : l ≠ t := by dsimp [t]; omega
  let u₁ := rootPreimage F p hp i t hit a
  let u₂ := rootPreimage F p hp t j htj 1
  have h₁ : p u₁ = rootImage F i t hit a := rootPreimage_map F p hp _ _ _ _
  have h₂ : p u₂ = rootImage F t j htj 1 := rootPreimage_map F p hp _ _ _ _
  have h12 : p ⁅u₁, u₂⁆ = p u := by
    rw [map_commutatorElement, h₁, h₂, rootImage_chain F i t j hit htj hij, mul_one, hu]
  have hcomm : Commute ⁅u₁, u₂⁆ v := by
    apply commutator_commutes p hc
    · rw [h₁, hv]
      exact rootImage_commute F i t k l hit hkl htk hli a b
    · rw [h₂, hv]
      exact rootImage_commute F t j k l htj hkl hjk hlt 1 b
  apply commutatorElement_eq_one_iff_commute.mp
  rw [← commutator_congr p hc h12 (rfl : p v = p v)]
  exact hcomm.commutator_eq

private def rootBracket (i k j : ℕ) (hik : i ≠ k) (hkj : k ≠ j) (a b : F) : H :=
  ⁅rootPreimage F p hp i k hik a, rootPreimage F p hp k j hkj b⁆

private lemma rootBracket_map (i k j : ℕ) (hik : i ≠ k) (hkj : k ≠ j)
    (hij : i ≠ j) (a b : F) :
    p (rootBracket F p hp i k j hik hkj a b) = rootImage F i j hij (a * b) := by
  rw [rootBracket, map_commutatorElement, rootPreimage_map, rootPreimage_map,
    rootImage_chain F i k j hik hkj hij]

include hc in
/-- Four distinct coordinates allow a factor to move through a triple commutator. -/
private lemma rootBracket_balance (i k l j : ℕ) (hik : i ≠ k) (hkj : k ≠ j)
    (hil : i ≠ l) (hlj : l ≠ j) (hkl : k ≠ l) (hij : i ≠ j) (a b c : F) :
    rootBracket F p hp i k j hik hkj (a * b) c =
      rootBracket F p hp i l j hil hlj a (b * c) := by
  let r := rootPreimage F p hp i l hil a
  let s := rootPreimage F p hp l k hkl.symm b
  let t := rootPreimage F p hp k j hkj c
  have hr : p r = rootImage F i l hil a := rootPreimage_map F p hp _ _ _ _
  have hs : p s = rootImage F l k hkl.symm b := rootPreimage_map F p hp _ _ _ _
  have ht : p t = rootImage F k j hkj c := rootPreimage_map F p hp _ _ _ _
  have hrs : p ⁅r, s⁆ = rootImage F i k hik (a * b) := by
    rw [map_commutatorElement, hr, hs, rootImage_chain F i l k hil hkl.symm hik]
  have hst : p ⁅s, t⁆ = rootImage F l j hlj (b * c) := by
    rw [map_commutatorElement, hs, ht, rootImage_chain F l k j hkl.symm hkj hlj]
  calc
    _ = ⁅⁅r, s⁆, t⁆ := by
      apply commutator_congr p hc
      · rw [rootPreimage_map, hrs]
      · rfl
    _ = ⁅r, ⁅s, t⁆⁆ := by
      apply commutator_assoc
      · exact preimages_commute F p hp hc i l k j hil hkj hkl.symm hij.symm a c hr ht
      · exact preimages_commute F p hp hc i k l j hik hlj hkl hij.symm
          (a * b) (b * c) hrs hst
      · exact preimages_commute F p hp hc l j k j hlj hkj hkj.symm hlj.symm
          (b * c) c hst ht
    _ = _ := by
      apply commutator_congr p hc
      · rfl
      · rw [rootPreimage_map, hst]

include hc in
private lemma rootBracket_independent (i k l j : ℕ) (hik : i ≠ k) (hkj : k ≠ j)
    (hil : i ≠ l) (hlj : l ≠ j) (hij : i ≠ j) (a : F) :
    rootBracket F p hp i k j hik hkj a 1 = rootBracket F p hp i l j hil hlj a 1 := by
  by_cases hkl : k = l
  · subst l
    rfl
  · simpa only [mul_one, one_mul] using
      rootBracket_balance F p hp hc i k l j hik hkj hil hlj hkl hij a 1 1

private def rootLift (i j : ℕ) (_hij : i ≠ j) (a : F) : H :=
  rootBracket F p hp i (max i j + 1) j (by omega) (by omega) a 1

private lemma rootLift_map (i j : ℕ) (hij : i ≠ j) (a : F) :
    p (rootLift F p hp i j hij a) = rootImage F i j hij a := by
  rw [rootLift, rootBracket_map F p hp i (max i j + 1) j _ _ hij, mul_one]

include hc in
private lemma rootLift_eq_bracket (i k j : ℕ) (hik : i ≠ k) (hkj : k ≠ j)
    (hij : i ≠ j) (a : F) :
    rootLift F p hp i j hij a = rootBracket F p hp i k j hik hkj a 1 :=
  rootBracket_independent F p hp hc i (max i j + 1) k j _ _ hik hkj hij a

include hc in
private lemma rootBracket_eq_rootLift (i k j : ℕ) (hik : i ≠ k) (hkj : k ≠ j)
    (hij : i ≠ j) (a b : F) :
    rootBracket F p hp i k j hik hkj a b = rootLift F p hp i j hij (a * b) := by
  let l := i + j + k + 1
  have hil : i ≠ l := by dsimp [l]; omega
  have hlj : l ≠ j := by dsimp [l]; omega
  have hlk : l ≠ k := by dsimp [l]; omega
  calc
    _ = rootBracket F p hp i l j hil hlj (a * b) 1 := by
      simpa only [mul_one] using
        (rootBracket_balance F p hp hc i l k j hil hlj hik hkj hlk hij a b 1).symm
    _ = _ := (rootLift_eq_bracket F p hp hc i l j hil hlj hij (a * b)).symm

include hc in
private lemma rootLift_commute (i j k l : ℕ) (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i) (a b : F) :
    Commute (rootLift F p hp i j hij a) (rootLift F p hp k l hkl b) :=
  preimages_commute F p hp hc i j k l hij hkl hjk hli a b
    (rootLift_map F p hp _ _ _ _) (rootLift_map F p hp _ _ _ _)

include hc in
private lemma rootLift_add (i j : ℕ) (hij : i ≠ j) (a b : F) :
    rootLift F p hp i j hij a * rootLift F p hp i j hij b =
      rootLift F p hp i j hij (a + b) := by
  let k := max i j + 1
  have hik : i ≠ k := by dsimp [k]; omega
  have hkj : k ≠ j := by dsimp [k]; omega
  let r := rootPreimage F p hp i k hik a
  let s := rootPreimage F p hp i k hik b
  let t := rootPreimage F p hp k j hkj 1
  have hr : p r = rootImage F i k hik a := rootPreimage_map F p hp _ _ _ _
  have hs : p s = rootImage F i k hik b := rootPreimage_map F p hp _ _ _ _
  have ht : p t = rootImage F k j hkj 1 := rootPreimage_map F p hp _ _ _ _
  have hrt : p ⁅r, t⁆ = rootImage F i j hij a := by
    rw [map_commutatorElement, hr, ht, rootImage_chain F i k j hik hkj hij, mul_one]
  have hcomm : Commute s ⁅r, t⁆ :=
    preimages_commute F p hp hc i k i j hik hij hik.symm hij.symm b a hs hrt
  calc
    _ = ⁅r, t⁆ * ⁅s, t⁆ := by
      rw [rootLift_eq_bracket F p hp hc i k j hik hkj hij a,
        rootLift_eq_bracket F p hp hc i k j hik hkj hij b]
      rfl
    _ = ⁅s * r, t⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul, hcomm.eq, mul_inv_cancel_right]
    _ = _ := by
      rw [rootLift_eq_bracket F p hp hc i k j hik hkj hij (a + b)]
      apply commutator_congr p hc
      · rw [map_mul, hs, hr, rootImage_add, rootPreimage_map, add_comm]
      · rfl

include hc in
private lemma rootLift_chain (i j k : ℕ) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a b : F) :
    ⁅rootLift F p hp i j hij a, rootLift F p hp j k hjk b⁆ =
      rootLift F p hp i k hik (a * b) := by
  calc
    _ = rootBracket F p hp i j k hij hjk a b := by
      apply commutator_congr p hc
      · rw [rootLift_map, rootPreimage_map]
      · rw [rootLift_map, rootPreimage_map]
    _ = _ := rootBracket_eq_rootLift F p hp hc i j k hij hjk hik a b

private def liftedGenerator (g : Generator F) : H :=
  rootLift F p hp g.row g.col (by simpa only [ne_eq, Fin.ext_iff] using g.ne) g.entry

include hc in
private lemma lifted_relations (r : FreeGroup (Generator F)) (hr : r ∈ relations F) :
    FreeGroup.lift (liftedGenerator F p hp) r = 1 := by
  cases hr with
  | rootAdd n i j hij a b =>
    simp only [map_mul, map_inv, word, FreeGroup.lift_apply_of, liftedGenerator]
    rw [rootLift_add F p hp hc, mul_inv_cancel]
  | disjoint n i j k l hij hkl hjk hli a b =>
    simp only [map_commutatorElement, word, FreeGroup.lift_apply_of, liftedGenerator]
    apply commutatorElement_eq_one_iff_commute.mpr
    exact rootLift_commute F p hp hc i j k l _ _
      (by simpa only [ne_eq, Fin.ext_iff] using hjk)
      (by simpa only [ne_eq, Fin.ext_iff] using hli) a b
  | chain n i j k hij hjk hik a b =>
    simp only [map_mul, map_inv, map_commutatorElement, word, FreeGroup.lift_apply_of,
      liftedGenerator]
    rw [rootLift_chain F p hp hc i j k _ _
      (by simpa only [ne_eq, Fin.ext_iff] using hik), mul_inv_cancel]
  | stabilize n i j hij a =>
    simp only [map_mul, map_inv, word, FreeGroup.lift_apply_of, liftedGenerator,
      Fin.val_castSucc, mul_inv_cancel]

/-- The lift of the actual stable Steinberg presentation to a surjective central extension
of the actual stable elementary subgroup. The construction uses commutators of preimages
of elementary roots; no Steinberg lifting law is an input. -/
@[no_expose] def liftToCentralExtension : Group F →* H :=
  PresentedGroup.toGroup (lifted_relations F p hp hc)

/-- The constructed lift lies over the original map to the actual elementary subgroup. -/
theorem liftToCentralExtension_over :
    p.comp (liftToCentralExtension F p hp hc) = toElementary F := by
  apply PresentedGroup.ext
  intro g
  rw [MonoidHom.comp_apply, liftToCentralExtension, PresentedGroup.toGroup.of]
  change p (liftedGenerator F p hp g) = toElementary F (x F g.rank g.row g.col g.ne g.entry)
  rw [liftedGenerator, rootLift_map, rootImage, natRoot_eq]

/-- On each original finite-rank generator, the lift is the commutator of any preimages
of its two elementary roots through the newly adjoined coordinate. -/
theorem liftToCentralExtension_x (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : F)
    (r s : H)
    (hr : p r = toElementary F
      (x F (n + 1) i.castSucc (Fin.last n) (Fin.castSucc_ne_last i) a))
    (hs : p s = toElementary F
      (x F (n + 1) (Fin.last n) j.castSucc (Fin.castSucc_ne_last j).symm 1)) :
    liftToCentralExtension F p hp hc (x F n i j hij a) = ⁅r, s⁆ := by
  have hover (g : Group F) :
      p (liftToCentralExtension F p hp hc g) = toElementary F g :=
    congrArg (fun f : Group F →* StableGeneralLinear.elementary F => f g)
      (liftToCentralExtension_over F p hp hc)
  rw [x_eq_commutator_succ, map_commutatorElement]
  exact commutator_congr p hc ((hover _).trans hr.symm) ((hover _).trans hs.symm)

include hc in
/-- Perfectness makes homomorphisms over the same central extension unique. -/
theorem liftToCentralExtension_unique (f g : Group F →* H)
    (hf : p.comp f = toElementary F) (hg : p.comp g = toElementary F) : f = g :=
  hom_ext_of_perfect p hc f g (hf.trans hg.symm)

include hp hc in
/-- The actual stable Steinberg presentation lifts uniquely through every surjective central
extension of the original stable elementary subgroup, including over fields of order two or three.
The extension group may lie in an independent universe. -/
theorem existsUnique_lift_toElementary :
    ∃! f : Group F →* H, p.comp f = toElementary F := by
  refine ⟨liftToCentralExtension F p hp hc, liftToCentralExtension_over F p hp hc, ?_⟩
  intro f hf
  exact liftToCentralExtension_unique F p hc f _ hf (liftToCentralExtension_over F p hp hc)

end Roots
end StableSteinberg

attribute [colib_ref "quillen" "Quillen/Algebra/Group/StableSteinbergUniversal.lean"
  "adaptation" "Actual central lift, its generator value and uniqueness"]
  StableSteinberg.liftToCentralExtension StableSteinberg.liftToCentralExtension_over
  StableSteinberg.liftToCentralExtension_x StableSteinberg.existsUnique_lift_toElementary
