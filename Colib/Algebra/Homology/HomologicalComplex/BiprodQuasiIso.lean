/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
Adapted from `Quillen/Aglib/Algebra/Homology/HomologicalComplex/BiprodQuasiIso.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps.
 # Binary sums preserve quasi-isomorphisms of actual chain maps -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits

namespace HomologicalComplex

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {K₁ K₂ L₁ L₂ : HomologicalComplex C c}

/-- Homology additivity makes the original binary-sum map a quasi-isomorphism. -/
theorem quasiIso_biprod_map (f : K₁ ⟶ L₁) (g : K₂ ⟶ L₂) [QuasiIso f] [QuasiIso g] :
    QuasiIso (biprod.map f g) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let F := homologyFunctor C c n
  have : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
  have : IsIso (F.map f) := inferInstanceAs (IsIso (homologyMap f n))
  have : IsIso (F.map g) := inferInstanceAs (IsIso (homologyMap g n))
  have : IsIso (biprod.map (F.map f) (F.map g)) :=
    (biprod.mapIso (asIso (F.map f)) (asIso (F.map g))).isIso_hom
  have h : F.map (biprod.map f g) = (F.mapBiprod K₁ K₂).hom ≫
      biprod.map (F.map f) (F.map g) ≫ (F.mapBiprod L₁ L₂).inv := by
    apply (cancel_mono (F.mapBiprod L₁ L₂).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply biprod.hom_ext <;>
      simp [Category.assoc, ← Functor.map_comp]
  change IsIso (F.map (biprod.map f g))
  rw [h]
  infer_instance

end HomologicalComplex
