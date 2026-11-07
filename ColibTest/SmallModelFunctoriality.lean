module

public import Colib.KTheory.Quillen.SmallModel.Functoriality

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory

universe w v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} {D : Type u₂} {T : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} T]
  [Preadditive C] [Preadditive D] [Preadditive T]
  [HasFiniteBiproducts C] [HasFiniteBiproducts D] [HasFiniteBiproducts T]
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D] [EssentiallySmall.{w} T]
  {EC : ExactStructure C} {ED : ExactStructure D} {ET : ExactStructure T}

-- Preserve the original small universe and independent ambient universes.
example (E : ExactStructure C) (n : ℕ) :
    (ExactFunctor.id E).smallKMap n = MonoidHom.id (E.SmallK n) :=
  ExactFunctor.smallKMap_id E n

example (F : ExactFunctor EC ED) (G : ExactFunctor ED ET) (n : ℕ) :
    (F.comp G).smallKMap n = (G.smallKMap n).comp (F.smallKMap n) :=
  ExactFunctor.smallKMap_comp F G n

example {F G : ExactFunctor EC ED} (e : F.toFunctor ≅ G.toFunctor) :
    F.smallKMap 0 = G.smallKMap 0 :=
  ExactFunctor.smallKMap_eq_of_natIso e 0
