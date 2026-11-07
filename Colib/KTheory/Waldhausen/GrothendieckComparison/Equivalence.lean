/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.GrothendieckComparison.Generation

/-! # The classical presentation computes genuine Waldhausen K₀

For every small Waldhausen category, the original object-loop comparison is
an equivalence between the original object/weak-arrow/cofibration-pushout
presentation and the unchanged homotopical K₀. Its inverse is precisely the
original realized grading map. All original exact functors are retained.

Implementation provenance: `Quillen/Waldhausen/GrothendieckComparison/Equivalence.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
objects, maps and hypotheses are retained.
-/
@[expose] public section

noncomputable section
open Topology SSet
open CategoryTheory
universe u v
namespace CategoryTheory.Waldhausen.AlgebraicGrothendieck
variable {C : Type u} [SmallCategory C] (W : Structure C)

/-- The original classical object-class comparison is bijective onto actual fine K₀. -/
theorem grothendieckToKZero_bijective : Function.Bijective (grothendieckToKZero W) :=
  ⟨grothendieckToKZero_injective W, grothendieckToKZero_surjective W⟩

/-- The original realized grading map is also a right inverse on every actual fine K₀ class. -/
@[simp] theorem grothendieckToKZero_comp :
    (grothendieckToKZero W).comp (kZeroToGrothendieck W) = MonoidHom.id (W.K 0) := by
  apply MonoidHom.ext
  intro x
  obtain ⟨a, rfl⟩ := grothendieckToKZero_surjective W x
  exact congrArg (grothendieckToKZero W) (DFunLike.congr_fun (kZeroToGrothendieck_comp W) a)

/-- The genuine canonical classical-to-homotopical equivalence, with the original
object-loop homomorphism and the original grading map as its inverse. -/
@[colib_tag "COL-0269"]
def grothendieckKZeroEquiv : Multiplicative (Group W) ≃* W.K 0 where
  toFun := grothendieckToKZero W
  invFun := kZeroToGrothendieck W
  left_inv := DFunLike.congr_fun (kZeroToGrothendieck_comp W)
  right_inv := DFunLike.congr_fun (grothendieckToKZero_comp W)
  map_mul' := (grothendieckToKZero W).map_mul

@[simp] theorem grothendieckKZeroEquiv_coe :
    (grothendieckKZeroEquiv W : Multiplicative (Group W) →* W.K 0) =
      grothendieckToKZero W := rfl

@[simp] theorem grothendieckKZeroEquiv_symm_coe :
    ((grothendieckKZeroEquiv W).symm : W.K 0 →* Multiplicative (Group W)) =
      kZeroToGrothendieck W := rfl

/-- The canonical equivalence retains the exact original object class. -/
@[simp] theorem grothendieckKZeroEquiv_objectClass (A : C) :
    grothendieckKZeroEquiv W (Multiplicative.ofAdd (objectClass W A)) =
      W.kZeroObjectClass A := grothendieckToKZero_objectClass W A

/-- The original realized grading comparison is injective on all actual fine classes. -/
theorem kZeroToGrothendieck_injective : Function.Injective (kZeroToGrothendieck W) :=
  (grothendieckKZeroEquiv W).symm.injective

/-- The original realized grading map itself is bijective. -/
theorem kZeroToGrothendieck_bijective : Function.Bijective (kZeroToGrothendieck W) :=
  (grothendieckKZeroEquiv W).symm.bijective

/-- Original object loops determine homomorphisms out of genuine fine K₀. -/
@[ext] theorem kZero_hom_ext {H : Type v} [_root_.Group H] (f g : W.K 0 →* H)
    (h : ∀ A, f (W.kZeroObjectClass A) = g (W.kZeroObjectClass A)) : f = g := by
  have hc : f.comp (grothendieckToKZero W) = g.comp (grothendieckToKZero W) := by
    apply mulHom_ext W
    intro A
    simpa only [MonoidHom.comp_apply, grothendieckToKZero_objectClass] using h A
  apply MonoidHom.ext
  intro x
  obtain ⟨a, rfl⟩ := grothendieckToKZero_surjective W x
  exact DFunLike.congr_fun hc a

variable {D : Type u} [SmallCategory D] (V : Structure D) (F : C ⥤ D)
  (hF : IsExact W.cof W.weq V.cof V.weq F)

/-- The genuine canonical equivalence respects every original exact-functor map. -/
theorem grothendieckKZeroEquiv_natural :
    (KMap hF 0).comp (grothendieckKZeroEquiv W : Multiplicative (Group W) →* W.K 0) =
      (grothendieckKZeroEquiv V : Multiplicative (Group V) →* V.K 0).comp
        (map W F hF).toMultiplicative := grothendieckToKZero_natural W V F hF

end CategoryTheory.Waldhausen.AlgebraicGrothendieck
