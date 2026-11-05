/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import StacksCore.CategoryTheory.GrothendieckGroup.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The Grothendieck group of finite-dimensional vector spaces

Dimension identifies the Grothendieck group of Mathlib's category of finite modules over a
field with the integers. See the field computation in Stacks Project, Tag 00JE.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory

namespace CategoryTheory.GrothendieckGroup

variable (k : Type u) [Field k]

/-- The dimension homomorphism on the Grothendieck group of finite-dimensional
vector spaces over a field. -/
def fgModuleRank : GrothendieckGroup (FGModuleCat.{u} k) →+ ℤ :=
  lift (fun V => Module.finrank k V) (by
    intro S hS
    let F := forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)
    let T := S.map F
    have hT : T.ShortExact := hS.map_of_exact F
    let : Module.Finite k T.X₂ := (inferInstance : Module.Finite k S.X₂)
    have h₁ : Module.finrank k (LinearMap.range T.f.hom) = Module.finrank k T.X₁ :=
      (LinearEquiv.ofInjective T.f.hom hT.moduleCat_injective_f).finrank_eq.symm
    have h₃ : Module.finrank k (LinearMap.range T.g.hom) = Module.finrank k T.X₃ := by
      rw [LinearMap.range_eq_top.mpr hT.moduleCat_surjective_g, finrank_top]
    have h := LinearMap.finrank_range_add_finrank_ker T.g.hom
    rw [← hT.exact.moduleCat_range_eq_ker, h₁, h₃, add_comm] at h
    exact_mod_cast h.symm)

/-- The dimension homomorphism sends the class of a vector space to its dimension. -/
@[simp] theorem fgModuleRank_of (V : FGModuleCat.{u} k) :
    fgModuleRank k (of V) = Module.finrank k V := rfl

/-- Dimension is an additive equivalence from the Grothendieck group of finite modules
over a field to the integers. -/
def fgModuleRankEquiv : GrothendieckGroup (FGModuleCat.{u} k) ≃+ ℤ :=
  AddEquiv.ofBijective (fgModuleRank k) (by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨V, W, rfl⟩ := exists_eq_of_sub_of x
      have hd : Module.finrank k V = Module.finrank k W := by
        have he : (Module.finrank k V : ℤ) = Module.finrank k W := by
          exact sub_eq_zero.mp (by simpa only [map_sub, fgModuleRank_of] using hx)
        exact_mod_cast he
      let e : V ≅ W := (LinearEquiv.ofFinrankEq V W hd).toFGModuleCatIso
      exact sub_eq_zero.mpr (of_eq_of_iso e)
    · intro n
      exact ⟨n • of (FGModuleCat.of k k), by simp [Module.finrank_self]⟩)

/-- The dimension equivalence is normalized by the class of each vector space. -/
@[simp] theorem fgModuleRankEquiv_of (V : FGModuleCat.{u} k) :
    fgModuleRankEquiv k (of V) = Module.finrank k V := fgModuleRank_of k V

end CategoryTheory.GrothendieckGroup
