import Colib.CategoryTheory.Waldhausen.SConstruction.WeakNaturalTransformationTriangle

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite MonoidalCategory
open scoped Simplicial

universe v u

namespace WaldhausenCompositionTriangleTests

open CategoryTheory.Waldhausen

section Zero

variable {C : Type u} [Category.{v} C] (cof weq : MorphismProperty C)
  [cof.ContainsIdentities] [weq.ContainsIdentities]

example (Z : C) (hZ : IsZero Z) (n : SimplexCategoryᵒᵖ) :
    (zeroSimplex cof weq Z hZ n).val = (Functor.const (Grid n.unop)).obj Z := rfl

end Zero

section Grids

variable {D : Type u} [Category.{v} D] (W : Structure D) {n m : SimplexCategory}
  {A B C : Grid₂ n m ⥤ D} (η : A ⟶ B) (θ : B ⟶ C)
  (hη : ∀ p, W.weq (η.app p)) (hθ : ∀ p, W.weq (θ.app p))
  (hA : IsSimplex₂ W.cof W.weq A) (hB : IsSimplex₂ W.cof W.weq B)
  (hC : IsSimplex₂ W.cof W.weq C)

-- Componentwise weakness, without invertibility or extra exactness of grid maps.
example (τ : m ⟶ ⦋2⦌) : IsSimplex₂ W.cof W.weq (nerveTriangleDiagram η θ τ) :=
  nerveTriangleDiagram_isSimplex₂ W η θ hη hθ hA hB hC τ

example (τ : m ⟶ ⦋1⦌) :
    nerveTriangleDiagram η θ (τ ≫ SimplexCategory.δ 2) = nerveCylinderDiagram η τ :=
  nerveTriangleDiagram_first η θ τ

example (τ : m ⟶ ⦋1⦌) :
    nerveTriangleDiagram η θ (τ ≫ SimplexCategory.δ 0) = nerveCylinderDiagram θ τ :=
  nerveTriangleDiagram_second η θ τ

example (τ : m ⟶ ⦋1⦌) :
    nerveTriangleDiagram η θ (τ ≫ SimplexCategory.δ 1) =
      nerveCylinderDiagram (η ≫ θ) τ :=
  nerveTriangleDiagram_composite η θ τ

-- Both independent reindexing directions, not just the diagonal.
example {n' m' : SimplexCategory} (α : n' ⟶ n) (β : m' ⟶ m) (τ : m ⟶ ⦋2⦌) :
    nerveTriangleDiagram (whiskerLeft (gridMap₂ α β) η)
        (whiskerLeft (gridMap₂ α β) θ) (β ≫ τ) =
      gridMap₂ α β ⋙ nerveTriangleDiagram η θ τ :=
  nerveTriangleDiagram_precomp η θ α β τ

example {n' : SimplexCategory} (α : n' ⟶ n) (τ : m ⟶ ⦋2⦌) :
    nerveTriangleDiagram (whiskerLeft (gridMap₂ α (𝟙 m)) η)
        (whiskerLeft (gridMap₂ α (𝟙 m)) θ) τ =
      gridMap₂ α (𝟙 m) ⋙ nerveTriangleDiagram η θ τ := by
  simpa only [Category.id_comp] using nerveTriangleDiagram_precomp η θ α (𝟙 m) τ

example {m' : SimplexCategory} (β : m' ⟶ m) (τ : m ⟶ ⦋2⦌) :
    nerveTriangleDiagram (whiskerLeft (gridMap₂ (𝟙 n) β) η)
        (whiskerLeft (gridMap₂ (𝟙 n) β) θ) (β ≫ τ) =
      gridMap₂ (𝟙 n) β ⋙ nerveTriangleDiagram η θ τ :=
  nerveTriangleDiagram_precomp η θ (𝟙 n) β τ

-- The full triangle is constant, without assumptions on zero components.
example (Z : D) (hZ : IsZero Z) (eA : ∀ p, A.obj p = Z) (eB : ∀ p, B.obj p = Z)
    (eC : ∀ p, C.obj p = Z) (τ : m ⟶ ⦋2⦌) :
    nerveTriangleDiagram η θ τ = (Functor.const (Grid₂ n m)).obj Z :=
  nerveTriangleDiagram_eq_const_of_zero η θ Z hZ eA eB eC τ

end Grids

section Families

variable {D : Type u} [Category.{v} D] (W : Structure D)
  {X : SimplexCategoryᵒᵖ ⥤ SSet.{max u v}} (f g h : X ⟶ bisimplicialSSet W)
  (η : ∀ (n m : SimplexCategoryᵒᵖ) (x : (X.obj n).obj m),
    (((f.app n).app m) x).1 ⟶ (((g.app n).app m) x).1)
  (θ : ∀ (n m : SimplexCategoryᵒᵖ) (x : (X.obj n).obj m),
    (((g.app n).app m) x).1 ⟶ (((h.app n).app m) x).1)
  (hη : ∀ n m x p, W.weq ((η n m x).app p))
  (hθ : ∀ n m x p, W.weq ((θ n m x).app p))
  (eη : ∀ {n n' : SimplexCategoryᵒᵖ} (α : n ⟶ n')
    (x : (SSet.diagonalSSet X).obj n) (p : Grid₂ n'.unop n'.unop),
    HEq ((η n' n' ((SSet.diagonalSSet X).map α x)).app p)
      ((η n n x).app ((gridMap₂ α.unop α.unop).obj p)))
  (eθ : ∀ {n n' : SimplexCategoryᵒᵖ} (α : n ⟶ n')
    (x : (SSet.diagonalSSet X).obj n) (p : Grid₂ n'.unop n'.unop),
    HEq ((θ n' n' ((SSet.diagonalSSet X).map α x)).app p)
      ((θ n n x).app ((gridMap₂ α.unop α.unop).obj p)))

example : SSet.diagonalSSet X ⊗ Δ[2] ⟶ SSet.diagonalSSet (bisimplicialSSet W) :=
  weakGridFamilyTriangle W f g h η θ hη hθ eη eθ

example :
    ((𝟙 (SSet.diagonalSSet X)) ⊗ₘ SSet.stdSimplex.δ 2) ≫
        weakGridFamilyTriangle W f g h η θ hη hθ eη eθ =
      weakGridFamilyCylinder W f g η hη eη :=
  weakGridFamilyTriangle_first W f g h η θ hη hθ eη eθ

example :
    ((𝟙 (SSet.diagonalSSet X)) ⊗ₘ SSet.stdSimplex.δ 0) ≫
        weakGridFamilyTriangle W f g h η θ hη hθ eη eθ =
      weakGridFamilyCylinder W g h θ hθ eθ :=
  weakGridFamilyTriangle_second W f g h η θ hη hθ eη eθ

example :
    ((𝟙 (SSet.diagonalSSet X)) ⊗ₘ SSet.stdSimplex.δ 1) ≫
        weakGridFamilyTriangle W f g h η θ hη hθ eη eθ =
      weakGridFamilyCylinder W f h (fun n m x ↦ η n m x ≫ θ n m x)
        (fun n m x p ↦ W.weq.comp_mem _ _ (hη n m x p) (hθ n m x p))
        (weakGridFamily_comp_compat W f g h η θ eη eθ) :=
  weakGridFamilyTriangle_composite W f g h η θ hη hθ eη eθ

end Families

section ExactFunctors

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) {F G H : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact V.cof V.weq W.cof W.weq G)
  (hH : IsExact V.cof V.weq W.cof W.weq H)
  (η : F ⟶ G) (θ : G ⟶ H)
  (hη : ∀ X, W.weq (η.app X)) (hθ : ∀ X, W.weq (θ.app X))

example : sSet V.cof V.weq ⊗ Δ[2] ⟶ sSet W.cof W.weq :=
  weakNaturalTransformationTriangle V W hF hG hH η θ hη hθ

example (n : SimplexCategoryᵒᵖ) (z : (sSet V.cof V.weq).obj n × (Δ[2]).obj n) :
    (TypeCat.Hom.hom (X := (sSet V.cof V.weq).obj n × (Δ[2]).obj n)
      ((weakNaturalTransformationTriangle V W hF hG hH η θ hη hθ).app n) z).val =
      nerveTriangleDiagram (whiskerLeft z.1.val η) (whiskerLeft z.1.val θ) z.2.down :=
  weakNaturalTransformationTriangle_app_val V W hF hG hH η θ hη hθ n z

example :
    ((𝟙 (sSet V.cof V.weq)) ⊗ₘ SSet.stdSimplex.δ 2) ≫
        weakNaturalTransformationTriangle V W hF hG hH η θ hη hθ =
      weakNaturalTransformationCylinder V W hF hG η hη :=
  weakNaturalTransformationTriangle_first V W hF hG hH η θ hη hθ

example :
    ((𝟙 (sSet V.cof V.weq)) ⊗ₘ SSet.stdSimplex.δ 0) ≫
        weakNaturalTransformationTriangle V W hF hG hH η θ hη hθ =
      weakNaturalTransformationCylinder V W hG hH θ hθ :=
  weakNaturalTransformationTriangle_second V W hF hG hH η θ hη hθ

example :
    ((𝟙 (sSet V.cof V.weq)) ⊗ₘ SSet.stdSimplex.δ 1) ≫
        weakNaturalTransformationTriangle V W hF hG hH η θ hη hθ =
      weakNaturalTransformationCylinder V W hF hH (η ≫ θ)
        (fun X ↦ W.weq.comp_mem _ _ (hη X) (hθ X)) :=
  weakNaturalTransformationTriangle_composite V W hF hG hH η θ hη hθ

-- Three explicit equalities are required for basedness, not for the triangle itself.
example (hF0 : F.obj V.zero = W.zero) (hG0 : G.obj V.zero = W.zero)
    (hH0 : H.obj V.zero = W.zero) :
    SSet.yonedaEquiv.symm (zeroSimplex V.cof V.weq V.zero V.isZero (op ⦋0⦌)) ▷ Δ[2] ≫
        weakNaturalTransformationTriangle V W hF hG hH η θ hη hθ =
      CartesianMonoidalCategory.fst Δ[0] Δ[2] ≫
        SSet.yonedaEquiv.symm (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌)) :=
  weakNaturalTransformationTriangle_fixed_zero V W hF hG hH η θ hη hθ hF0 hG0 hH0

end ExactFunctors

end WaldhausenCompositionTriangleTests
