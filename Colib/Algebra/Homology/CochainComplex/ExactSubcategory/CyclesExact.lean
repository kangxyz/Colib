/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Pullbacks
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.AcyclicTruncation
public import Colib.Algebra.Homology.CochainComplex.Cycles

/-!
# Exact cycle functors on actual acyclic complexes

For an ambient short exact sequence of cochain complexes, acyclicity of
only its right term makes the sequence of actual cycle objects short exact.
This constructs an actual exact functor from bounded acyclic termwise-P
complexes to the inherited exact full subcategory P.
-/
/-! Adapted from
`Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.CyclesExact`
at pinned Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe v u

namespace CochainComplex

attribute [local instance] Abelian.hasFiniteBiproducts

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The factorization of the differential through cycles is natural in
arbitrary actual chain maps. -/
@[reassoc]
theorem toCycles_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) (i j : ℤ) :
    K.toCycles i j ≫ cyclesMap f j = f.f i ≫ L.toCycles i j := by
  rw [← cancel_mono (L.iCycles j)]
  simp only [Category.assoc, cyclesMap_i, toCycles_i_assoc, toCycles_i, Hom.comm]

/-- Only exactness of the target degree and an epi in the preceding term
are required for the actual cycle map to be an epimorphism. -/
theorem cyclesMap_epi_of_exactAt {K L : CochainComplex A ℤ} (f : K ⟶ L)
    (i n : ℤ) (hin : i + 1 = n) [Epi (f.f i)] (hL : L.ExactAt n) :
    Epi (cyclesMap f n) := by
  subst n
  let : Epi (L.toCycles i (i + 1)) := _root_.CochainComplex.epi_toCycles_of_exactAt L i hL
  exact epi_of_epi_fac (toCycles_naturality f i (i + 1))

/-- The sequence of cycles is short exact when the rightmost complex is
acyclic. No exactness assumption on the middle complex is needed. -/
theorem cycles_shortExact (S : ShortComplex (CochainComplex A ℤ))
    (hS : S.ShortExact) (h₃ : S.X₃.Acyclic) (n : ℤ) :
    (S.map (cyclesFunctor A (ComplexShape.up ℤ) n)).ShortExact := by
  let := hS.mono_f
  let := hS.epi_g
  exact {
    mono_f := inferInstanceAs (Mono (cyclesMap S.f n))
    epi_g := cyclesMap_epi_of_exactAt S.g (n - 1) n (by omega) (h₃ n)
    exact := cycles_left_exact S hS.exact n }

/-- The actual cycles functor is additive. -/
instance cyclesFunctor_additive (n : ℤ) : (cyclesFunctor A (ComplexShape.up ℤ) n).Additive where
  map_add {K L} f g := by
    change cyclesMap (f + g) n = cyclesMap f n + cyclesMap g n
    rw [← cancel_mono (L.iCycles n)]
    simp only [cyclesMap_i, Preadditive.add_comp]
    change K.iCycles n ≫ (f.f n + g.f n) = _
    simp only [Preadditive.comp_add]

variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsKernelClosed P]

/-- The actual cycle functor restricted to bounded acyclic termwise-P complexes. -/
def boundedAcyclicCyclesFunctor (n : ℤ) : (boundedAcyclic P).FullSubcategory ⥤ P.FullSubcategory :=
  P.lift ((boundedAcyclic P).ι ⋙ cyclesFunctor A (ComplexShape.up ℤ) n) (fun K ↦ by
    obtain ⟨a, b, hab⟩ := K.property.1
    exact _root_.CochainComplex.cycles_mem P K.obj K.property.2.1 K.property.2.2 b
      (fun i hi ↦ hab i (Or.inr hi)) n)

instance boundedAcyclicCyclesFunctor_additive (n : ℤ) :
    (boundedAcyclicCyclesFunctor P n).Additive :=
  inferInstanceAs (Functor.Additive (P.lift _ _))

variable [(abelianExactStructure A).IsExtensionClosed P]

local instance : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P

/-- The actual cycle functor preserves the inherited conflations. -/
def boundedAcyclicCyclesExactFunctor (n : ℤ) :
    ExactFunctor (boundedAcyclicExactStructure P)
      (ExactSubcategory.exactStructure (abelianExactStructure A) P) where
  toFunctor := boundedAcyclicCyclesFunctor P n
  map_conflation S hS :=
    cycles_shortExact (S.map (boundedAcyclic P).ι) hS S.X₃.property.2.2 n

end CochainComplex
