/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremA.CommaChains
public import Colib.CategoryTheory.TheoremA.RealizationRows

/-! Source: Quillen/CategoryTheory/TheoremA/Columns.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps and universal properties retained. -/

/-!
# The other rows in Quillen's bisimplicial resolution

After fixing a source-chain dimension and transposing the replacement,
the summands are nerves of under categories with initial objects. This is
the second half of the rowwise calculation in the bisimplicial proof.
-/
@[expose] public section

noncomputable section

open SSet CategoryTheory Opposite
open scoped Simplicial

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.TheoremA

variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- The horizontal simplicial set obtained by fixing the comma-chain dimension. -/
def commaColumn (q : SimplexCategoryᵒᵖ) : SSet.{u} :=
  (simplicialReplacement (commaNerveDiagram F)).flip.obj q

/-- The under-category decomposition of a fixed column. -/
def commaColumnSummands (q : SimplexCategoryᵒᵖ) : SSet.{u} :=
  SSet.simplicialSigma fun c : ComposableArrows C q.unop.len ↦
    nerve (StructuredArrow (F.obj (c.obj (Fin.last q.unop.len))) (𝟭 D))

/-- The two descriptions of an individual bisimplex. -/
def commaColumnSimplexEquiv (p q : SimplexCategoryᵒᵖ) :
    (commaColumn F q).obj p ≃ (commaColumnSummands F q).obj p :=
  (Equiv.sigmaCongrRight (fun s : ComposableArrows D p.unop.len ↦
    commaChainEquiv F (s.obj 0) q.unop.len)).trans <|
  (show (Σ s : ComposableArrows D p.unop.len,
      Σ c : ComposableArrows C q.unop.len, F.obj (c.obj (Fin.last q.unop.len)) ⟶ s.obj 0) ≃
      (Σ c : ComposableArrows C q.unop.len,
      Σ s : ComposableArrows D p.unop.len, F.obj (c.obj (Fin.last q.unop.len)) ⟶ s.obj 0) from
    { toFun := fun x ↦ ⟨x.2.1, x.1, x.2.2⟩
      invFun := fun x ↦ ⟨x.2.1, x.1, x.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }).trans <|
  Equiv.sigmaCongrRight fun c : ComposableArrows C q.unop.len ↦
    (structuredChainEquiv (𝟭 D) (F.obj (c.obj (Fin.last q.unop.len))) p.unop.len).symm

/-- The under-category decomposition respects every horizontal simplicial operator. -/
def commaColumnIso (q : SimplexCategoryᵒᵖ) :
    commaColumn F q ≅ commaColumnSummands F q :=
  NatIso.ofComponents (fun p ↦ (commaColumnSimplexEquiv F p q).toIso) (by
    intro p r α
    ext x : 3
    change
      (⟨x.2 ⋙ CostructuredArrow.proj F (x.1.obj 0),
        structuredChainOfFirst (𝟭 D)
          ((SimplexCategory.toCat.map α.unop).toFunctor ⋙ x.1)
          ((x.2.obj (Fin.last q.unop.len)).hom ≫ firstVertexEdge α x.1)⟩ :
        (commaColumnSummands F q).obj r) =
      ⟨x.2 ⋙ CostructuredArrow.proj F (x.1.obj 0),
        (SimplexCategory.toCat.map α.unop).toFunctor ⋙
          structuredChainOfFirst (𝟭 D) x.1 (x.2.obj (Fin.last q.unop.len)).hom⟩
    apply congrArg (Sigma.mk _)
    refine CategoryTheory.Functor.ext (fun i ↦ ?_) ?_
    · refine StructuredArrow.obj_ext _ _ rfl ?_
      dsimp [structuredChainOfFirst, firstVertexEdge]
      rw [Category.comp_id]
      rw [Category.assoc, ← x.1.map_comp]
      rfl
    · intro i j f
      apply StructuredArrow.hom_ext
      simp [structuredChainOfFirst])

end CategoryTheory.TheoremA
