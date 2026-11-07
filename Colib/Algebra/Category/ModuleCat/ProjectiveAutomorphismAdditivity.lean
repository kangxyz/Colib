/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.ProjectiveAutomorphismClass
public import Colib.LinearAlgebra.Matrix.IdempotentSplitExtension
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveBaseChangeExact

/-!
Implementation provenance:
`Quillen/Algebra/Category/ModuleCat/ProjectiveAutomorphismAdditivity.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Additivity of actual projective automorphism classes

Identity extension through a split summand preserves the stable matrix class.
Consequently the actual direct-sum automorphism has the product of the classes.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
namespace Matrix.RightModule
variable {R : Type u} [Ring R]

/-- Identity extension along an actual projective retract preserves its stable class. -/
lemma projectiveAutomorphismClass_splitExtension
    {P Q : ModuleCat.FiniteProjective.Category.{u, u} Rᵐᵒᵖ}
    (i : P ⟶ Q) (r : Q ⟶ P) (hr : i ≫ r = 𝟙 P) (g : Aut P) (h : Aut Q)
    (hh : h.hom = r ≫ g.hom ≫ i + 𝟙 Q - r ≫ i) :
    projectiveAutomorphismClass Q h = projectiveAutomorphismClass P g := by
  let F := (imageEquivalence (R := R)).inverse
  apply automorphismClass_splitExtension (F.map i) (F.map r)
    (by rw [← F.map_comp, hr, F.map_id]) (F.mapIso g) (F.mapIso h)
  have he := congrArg (fun f => F.map f) hh
  simp only [Functor.map_sub, Functor.map_add, Functor.map_comp] at he
  have hid : F.map (𝟙 Q) = 𝟙 (F.obj Q) := F.map_id Q
  rw [hid] at he
  have he' := congrArg (CategoryTheory.Idempotents.Karoubi.inclusionHom (F.obj Q) (F.obj Q)) he
  simp only [map_sub, map_add, CategoryTheory.Idempotents.Karoubi.inclusionHom_apply,
    CategoryTheory.Idempotents.Karoubi.comp_f, CategoryTheory.Idempotents.Karoubi.id_f] at he'
  change homMatrix (F.map h.hom) =
    (homMatrix (F.map i) * homMatrix (F.map g.hom)) * homMatrix (F.map r) +
      idempotentMatrix (F.obj Q) - homMatrix (F.map i) * homMatrix (F.map r) at he'
  simpa only [Functor.mapIso_hom, Matrix.mul_assoc] using he'

/-- Adding an identity right summand preserves the actual stable automorphism class. -/
lemma projectiveAutomorphismClass_coprod_one
    (P Q : ModuleCat.FiniteProjective.Category.{u, u} Rᵐᵒᵖ) (g : Aut P) :
    projectiveAutomorphismClass (P ⨿ Q) (coprod.mapIso g (Iso.refl Q)) =
      projectiveAutomorphismClass P g := by
  apply projectiveAutomorphismClass_splitExtension coprod.inl (coprod.desc (𝟙 P) 0)
    (by simp) g _
  apply coprod.hom_ext <;>
    simp [Preadditive.comp_add, Preadditive.comp_sub]

/-- Adding an identity left summand preserves the actual stable automorphism class. -/
lemma projectiveAutomorphismClass_one_coprod
    (P Q : ModuleCat.FiniteProjective.Category.{u, u} Rᵐᵒᵖ) (g : Aut Q) :
    projectiveAutomorphismClass (P ⨿ Q) (coprod.mapIso (Iso.refl P) g) =
      projectiveAutomorphismClass Q g := by
  apply projectiveAutomorphismClass_splitExtension coprod.inr (coprod.desc 0 (𝟙 Q))
    (by simp) g _
  apply coprod.hom_ext <;>
    simp [Preadditive.comp_add, Preadditive.comp_sub]

/-- The actual direct sum of projective automorphisms gives the product of stable classes. -/
theorem projectiveAutomorphismClass_coprod
    (P Q : ModuleCat.FiniteProjective.Category.{u, u} Rᵐᵒᵖ) (g : Aut P) (h : Aut Q) :
    projectiveAutomorphismClass (P ⨿ Q) (coprod.mapIso g h) =
      projectiveAutomorphismClass P g * projectiveAutomorphismClass Q h := by
  let a : Aut (P ⨿ Q) := coprod.mapIso g (Iso.refl Q)
  let b : Aut (P ⨿ Q) := coprod.mapIso (Iso.refl P) h
  have he : (coprod.mapIso g h : Aut (P ⨿ Q)) = a * b := by
    apply Iso.ext
    change (coprod.mapIso g h).hom = b.hom ≫ a.hom
    apply coprod.hom_ext <;> simp [a, b]
  change projectiveAutomorphismClass (P ⨿ Q) (coprod.mapIso g h : Aut (P ⨿ Q)) = _
  rw [he, map_mul]
  exact congrArg₂ (· * ·) (projectiveAutomorphismClass_coprod_one P Q g)
    (projectiveAutomorphismClass_one_coprod P Q h)

end Matrix.RightModule
