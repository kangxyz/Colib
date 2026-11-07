/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.Loop.LeftComponentTranslation
public import Colib.Topology.Homotopy.HomotopyGroup.BasedHomotopyInverse

/-!
# Inverse-prefix normalization of an original loop component

Left concatenation with the inverse of a displayed loop sends that loop to its explicit
inverse-prefix concatenation. Standard cancellation then reaches the constant loop. The resulting
homotopy-group equivalence is the inverse of the original left-component equivalence. Its map,
basepoint correction, and comparison with the existing construction are all retained.
-/
/-! Implementation source:
`Quillen/Topology/HomotopyGroups/Loop/InverseComponentTranslation.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, basepoints,
coordinate order and signs are retained under native Colib ownership. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology
universe u v
namespace Topology
variable {X : Type u} [TopologicalSpace X] {x : X}

/-- The existing left-translation inverse is exactly left translation by the reversed loop. -/
theorem loopLeftTranslationEquiv_invFun (γ : Path x x) :
    (loopLeftTranslationEquiv γ).invFun = (loopLeftTranslationEquiv γ.symm).toFun := by
  apply ContinuousMap.ext
  intro δ
  rw [loopLeftTranslationEquiv_apply]
  change ((((γ.symm).symm).symm.trans δ.symm.symm).symm).symm = _
  simp only [Path.symm_symm]

/-- The displayed standard cancellation starts at the inverse-prefixed loop, not at the loop.
-/
def loopInversePrefixCancellation (γ : Path x x) :
    Path (γ.symm.trans γ) (Path.refl x) where
  toFun s := (Path.Homotopy.reflSymmTrans γ).symm.eval s
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    exact (Path.Homotopy.reflSymmTrans γ).symm.continuous
  source' := Path.Homotopy.eval_zero _
  target' := Path.Homotopy.eval_one _

/-- The actual inverse prefix and its cancellation normalize the displayed loop component. -/
def loopInversePrefixHomotopyEquiv (γ : Path x x) (n : ℕ) :
    HomotopyGroup.Pi n (Path x x) γ ≃
      HomotopyGroup.Pi n (Path x x) (Path.refl x) :=
  (Equiv.ofBijective
    (HomotopyGroup.map (loopLeftTranslationEquiv γ.symm).toFun
      (loopLeftTranslationEquiv_apply _ _))
    (homotopyGroupMap_bijective_of_homotopyEquiv (loopLeftTranslationEquiv γ.symm)
      (loopLeftTranslationEquiv_apply _ _) n)).trans
    (pathTransport (loopInversePrefixCancellation γ) n)

private theorem correctedMap_cast {A : Type u} {B : Type v}
    [TopologicalSpace A] [TopologicalSpace B] (f : C(A, B))
    {a : A} {b c : B} (h : f a = b) (p : Path b c) (n : ℕ)
    (α : HomotopyGroup.Pi n A a) :
    pathTransport (p.cast h rfl) n (HomotopyGroup.map f rfl α) =
      pathTransport p n (HomotopyGroup.map f h α) := by
  subst b
  rfl

private theorem correctedMap_congr {A : Type u} {B : Type v}
    [TopologicalSpace A] [TopologicalSpace B] {f g : C(A, B)} (h : f = g)
    {a : A} {b : B} (p : Path (f a) b) (q : Path (g a) b)
    (hpq : ∀ t, p t = q t) (n : ℕ) (α : HomotopyGroup.Pi n A a) :
    pathTransport p n (HomotopyGroup.map f rfl α) =
      pathTransport q n (HomotopyGroup.map g rfl α) := by
  subst g
  have he : p = q := Path.ext (funext hpq)
  subst q
  rfl

private theorem loop_pathTransport_eq {γ δ : Path x x} (p q : Path γ δ) (n : ℕ)
    (a : HomotopyGroup.Pi n (Path x x) γ) :
    pathTransport p n a = pathTransport q n a := by
  obtain ⟨b, rfl⟩ := (loopComponentHomotopyEquiv γ n).surjective a
  exact (loopComponentHomotopyEquiv_pathTransport p n b).trans
    (loopComponentHomotopyEquiv_pathTransport q n b).symm

/-- Inverse-prefix cancellation reverses the existing component translation in every degree.
The proof compares its actual correction with the original inverse homotopy, rather than assuming
that either translation fixes the chosen basepoint. -/
theorem loopInversePrefixHomotopyEquiv_leftComponent (γ : Path x x) (n : ℕ)
    (a : HomotopyGroup.Pi n (Path x x) (Path.refl x)) :
    loopInversePrefixHomotopyEquiv γ n (loopLeftComponentHomotopyEquiv γ n a) = a := by
  let e := loopLeftTranslationEquiv γ
  let g := (loopLeftTranslationEquiv γ.symm).toFun
  let p : Path (e (Path.refl x)) γ :=
    (loopRightUnitPath γ).cast (loopLeftTranslationEquiv_apply _ _) rfl
  let H := Classical.choice e.left_inv
  let d := (p.symm.map e.invFun.continuous).trans (H.evalAt (Path.refl x))
  have hg : e.invFun = g := loopLeftTranslationEquiv_invFun γ
  have hi : e.invFun γ = γ.symm.trans γ :=
    (ContinuousMap.congr_fun hg γ).trans (loopLeftTranslationEquiv_apply _ _)
  let c : Path (e.invFun γ) (Path.refl x) :=
    (loopInversePrefixCancellation γ).cast hi rfl
  let q : Path (g γ) (Path.refl x) :=
    (loopInversePrefixCancellation γ).cast (loopLeftTranslationEquiv_apply _ _) rfl
  have hf : pathTransport p n (HomotopyGroup.map e.toFun rfl a) =
      loopLeftComponentHomotopyEquiv γ n a :=
    correctedMap_cast e.toFun (loopLeftTranslationEquiv_apply _ _) (loopRightUnitPath γ) n a
  have h := pathTransport_homotopyEquiv_inverse e (Path.refl x) γ p H n a
  rw [hf] at h
  let b := loopLeftComponentHomotopyEquiv γ n a
  change pathTransport (loopInversePrefixCancellation γ) n
    (HomotopyGroup.map g (loopLeftTranslationEquiv_apply _ _) b) = a
  calc
    _ = pathTransport q n (HomotopyGroup.map g rfl b) :=
      (correctedMap_cast g (loopLeftTranslationEquiv_apply _ _)
        (loopInversePrefixCancellation γ) n b).symm
    _ = pathTransport c n (HomotopyGroup.map e.invFun rfl b) :=
      (correctedMap_congr hg c q (fun _ ↦ rfl) n b).symm
    _ = pathTransport d n (HomotopyGroup.map e.invFun rfl b) :=
      loop_pathTransport_eq c d n _
    _ = a := h

/-- The explicit normalization is precisely the inverse of the previously specified equivalence.
-/
theorem loopInversePrefixHomotopyEquiv_eq (γ : Path x x) (n : ℕ) :
    loopInversePrefixHomotopyEquiv γ n = (loopLeftComponentHomotopyEquiv γ n).symm := by
  apply Equiv.ext
  intro a
  obtain ⟨b, rfl⟩ := (loopLeftComponentHomotopyEquiv γ n).surjective a
  exact (loopInversePrefixHomotopyEquiv_leftComponent γ n b).trans
    ((loopLeftComponentHomotopyEquiv γ n).symm_apply_apply b).symm

end Topology
