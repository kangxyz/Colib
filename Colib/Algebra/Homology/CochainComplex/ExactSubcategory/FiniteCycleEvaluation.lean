/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Pullbacks
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.FiniteCycleFiltration

/-! # Actual cycle evaluation and disk insertion in finite acyclic strata

The free disk coordinate is its upper cycle. Original cycle evaluation and
original disk insertion are exact, their same-coordinate composite is
naturally identity, and their other-coordinate composites are naturally zero.
All endpoint cycle vanishing is derived from actual bounds and acyclicity.
-/
/-! Adapted from
`Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.FiniteCycleEvaluation`
at pinned Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ZeroObject
universe v u
namespace CochainComplex
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsKernelClosed P]

/-- Evaluation at the actual original cycle object. -/
def finiteCycleEvaluation (a b n : ℤ) :
    (fixedAcyclicBounds P a b).FullSubcategory ⥤ P.FullSubcategory :=
  (fixedAcyclicBounds P a b).ι ⋙ boundedAcyclicCyclesFunctor P n

omit [P.ContainsZero] in
@[simp] theorem finiteCycleEvaluation_map (a b n : ℤ)
    {K L : (fixedAcyclicBounds P a b).FullSubcategory} (f : K ⟶ L) :
    ((finiteCycleEvaluation P a b n).map f).hom = cyclesMap f.hom.hom n := rfl

instance finiteCycleEvaluation_additive (a b n : ℤ) : (finiteCycleEvaluation P a b n).Additive :=
  inferInstanceAs (Functor.Additive (_ ⋙ _))

/-- Insert the original identity disk in two allowed consecutive degrees. -/
def finiteCycleDisk (a b n : ℤ) (ha : a ≤ n) (hb : n + 1 ≤ b) :
    P.FullSubcategory ⥤ (fixedAcyclicBounds P a b).FullSubcategory :=
  (fixedAcyclicBounds P a b).lift (boundedAcyclicDiskFunctor P n)
    (fun X i hi ↦ identityDisk_isZero n X.obj i (by rcases hi with hi | hi <;> omega)
      (by rcases hi with hi | hi <;> omega))

omit [(abelianExactStructure A).IsKernelClosed P] in
@[simp] theorem finiteCycleDisk_map (a b n : ℤ) (ha : a ≤ n) (hb : n + 1 ≤ b)
    {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    ((finiteCycleDisk P a b n ha hb).map f).hom.hom = identityDiskMap n f.hom := rfl

instance finiteCycleDisk_additive (a b n : ℤ) (ha : a ≤ n) (hb : n + 1 ≤ b) :
    (finiteCycleDisk P a b n ha hb).Additive :=
  inferInstanceAs (Functor.Additive ((fixedAcyclicBounds P a b).lift _ _))

/-- The disk's actual upper cycle is naturally the original inserted object. -/
def finiteCycleDiskEvaluationIso (a b n : ℤ) (ha : a ≤ n) (hb : n + 1 ≤ b) :
    finiteCycleDisk P a b n ha hb ⋙ finiteCycleEvaluation P a b (n + 1) ≅ 𝟭 P.FullSubcategory :=
  NatIso.ofComponents (fun X ↦ P.isoMk (identityDiskCyclesIso n X.obj)) (by
    intro X Y f
    apply ObjectProperty.hom_ext
    exact (identityDiskCyclesNatIso n).hom.naturality f.hom)

/-- Every different actual cycle of the original disk is naturally zero. -/
def finiteCycleDiskEvaluationZeroIso (a b n : ℤ) (ha : a ≤ n) (hb : n + 1 ≤ b)
    (j : ℤ) (hj : j ≠ n + 1) :
    finiteCycleDisk P a b n ha hb ⋙ finiteCycleEvaluation P a b j ≅
      (Functor.const P.FullSubcategory).obj (0 : P.FullSubcategory) :=
  NatIso.ofComponents (fun X ↦ P.isoMk ((identityDisk_cycles_isZero n X.obj j hj).iso
    (P.ι.map_isZero (isZero_zero _)))) (by
      intro X Y f
      apply ObjectProperty.hom_ext
      exact (identityDisk_cycles_isZero n X.obj j hj).eq_of_src _ _)

/-- Cycles outside the genuine interior interval induce the actual zero functor. -/
def finiteCycleEvaluationZeroIso (a b n : ℤ) (hn : n ≤ a ∨ b < n) :
    finiteCycleEvaluation P a b n ≅
      (Functor.const (fixedAcyclicBounds P a b).FullSubcategory).obj (0 : P.FullSubcategory) :=
  NatIso.ofComponents (fun K ↦ P.isoMk
    ((K.property.cycles_isZero_outside K.obj.property.2.2 hn).iso
      (P.ι.map_isZero (isZero_zero _)))) (by
        intro K L f
        apply ObjectProperty.hom_ext
        exact (K.property.cycles_isZero_outside K.obj.property.2.2 hn).eq_of_src _ _)

variable [(abelianExactStructure A).IsExtensionClosed P]
local instance finiteCycleEvaluation_termPropertyProducts : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P

/-- Upper-cycle evaluation followed by original disk insertion is the actual layer. -/
theorem finiteCycleEvaluation_disk (a b n : ℤ) (ha : a ≤ n) (hb : n + 1 ≤ b) :
    finiteCycleEvaluation P a b (n + 1) ⋙ finiteCycleDisk P a b n ha hb = finiteCycleLayer P a b
      n := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- The original cycle functor preserves inherited conflations. -/
def finiteCycleEvaluationExact (a b n : ℤ) :
    ExactFunctor (fixedAcyclicExactStructure P a b)
      (ExactSubcategory.exactStructure (abelianExactStructure A) P) :=
  (fixedAcyclicInclusionExactFunctor P a b).comp (boundedAcyclicCyclesExactFunctor P n)

/-- The original disk functor preserves inherited conflations. -/
def finiteCycleDiskExact (a b n : ℤ) (ha : a ≤ n) (hb : n + 1 ≤ b) :
    ExactFunctor (ExactSubcategory.exactStructure (abelianExactStructure A) P)
      (fixedAcyclicExactStructure P a b) where
  toFunctor := finiteCycleDisk P a b n ha hb
  map_conflation S hS := (boundedAcyclicDiskExactFunctor P n).map_conflation S hS

end CochainComplex
