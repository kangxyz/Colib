/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.StableGeneralLinear
public import Colib.Topology.ClassifyingSpace.CofinalSequence
public import Colib.CategoryTheory.TheoremA.ContractibleComma
public import Mathlib.CategoryTheory.Grothendieck

/-!
# The finite-rank Grothendieck model of the stable general linear group

Implementation provenance: `Quillen/Topology/ClassifyingSpace/StableGeneralLinearGrothendieck.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps and universes are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory

namespace StableGeneralLinear.GrothendieckModel
variable (R : Type u) [Ring R]

/-- The actual Grothendieck construction of the finite-rank matrix group diagram. -/
abbrev Telescope := CategoryTheory.Grothendieck (categoryDiagram R)

private lemma eqToHom_down {G : Type u} [_root_.Group G]
    {X Y : AsSmall.{0} (SingleObj G)} (h : X = Y) :
    (eqToHom h).down = (1 : G) := by
  subst h
  rfl

private lemma comp_down {G : Type u} [_root_.Group G]
    {X Y Z : AsSmall.{0} (SingleObj G)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).down = g.down * f.down := rfl

/-- Send a finite-stage arrow to its original image in the stable group. -/
def projection : Telescope R ⥤ stableCategory R where
  obj _ := AsSmall.up.obj (SingleObj.star (Group R))
  map {X Y} f := ULift.up (of R (rank Y.base) f.fiber.down)
  map_id X := by
    apply ULift.ext
    simp only [CategoryTheory.Grothendieck.id_fiber]
    dsimp only [categoryDiagram, smallFunctor, Functor.toCatHom_toFunctor] at *
    rw [eqToHom_down, map_one]
    rfl
  map_comp {X Y Z} f g := by
    rcases X with ⟨x, ⟨⟨⟩⟩⟩
    rcases Y with ⟨y, ⟨⟨⟩⟩⟩
    rcases Z with ⟨z, ⟨⟨⟩⟩⟩
    apply ULift.ext
    change of R (rank z)
      (@Mul.mul (Matrix.GeneralLinearGroup (Fin (rank z)) R) _
        (@Mul.mul (Matrix.GeneralLinearGroup (Fin (rank z)) R) _ g.fiber.down
          (transition R (rank y) (rank z) (leOfHom (AsSmall.down.map g.base)) f.fiber.down)) 1) =
      of R (rank z) g.fiber.down * of R (rank y) f.fiber.down
    exact (congrArg (of R (rank z))
      (mul_one (M := Matrix.GeneralLinearGroup (Fin (rank z)) R) _)).trans
      ((map_mul (of R (rank z)) _ _).trans
        (congrArg (fun t => of R (rank z) g.fiber.down * t)
          (of_transition R _ f.fiber.down)))

/-- The projection restricts to the original stable inclusion on each fiber. -/
lemma inclusion_projection (n : ℕ) :
    CategoryTheory.Grothendieck.ι (categoryDiagram R) (rankIndex n) ⋙ projection R =
      smallFunctor (of R n) := by
  refine CategoryTheory.Functor.ext (fun X => by rcases X with ⟨⟨⟩⟩; rfl) ?_
  intro X Y f
  rcases X with ⟨⟨⟩⟩
  rcases Y with ⟨⟨⟩⟩
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  apply ULift.ext
  change of R n (@Mul.mul (Matrix.GeneralLinearGroup (Fin n) R) _ f.down 1) = of R n f.down
  exact congrArg (of R n) (mul_one (M := Matrix.GeneralLinearGroup (Fin n) R) _)

/-- The canonical object of the stable one-object category. -/
abbrev star : stableCategory R := AsSmall.up.obj (SingleObj.star (Group R))

/-- The comma category used by the original projection in Quillen's theorem A. -/
abbrev Comma := CostructuredArrow (projection R) (star R)

instance comma_thin : Quiver.IsThin (Comma R) := by
  intro a b
  constructor
  intro f g
  apply CostructuredArrow.hom_ext
  have hb : f.left.base = g.left.base := ULift.ext (Subsingleton.elim _ _)
  have hw := congrArg ULift.down ((CostructuredArrow.w f).trans
    (CostructuredArrow.w g).symm)
  have hp : of R (rank b.left.base) f.left.fiber.down =
      of R (rank b.left.base) g.left.fiber.down := by
    exact @mul_left_cancel (Group R) _ _ b.hom.down _ _ hw
  have hv := of_injective R (rank b.left.base) hp
  apply CategoryTheory.Grothendieck.ext _ _ hb
  apply ULift.ext
  rw [comp_down, eqToHom_down]
  exact (mul_one (M := Matrix.GeneralLinearGroup (Fin (rank b.left.base)) R) _).trans hv

/-- The standard object at a fixed rank, with identity structure arrow. -/
def standard (n : ℕ) : Comma R :=
  CostructuredArrow.mk (Y := ⟨rankIndex n, AsSmall.up.obj (SingleObj.star _)⟩) (𝟙 _)

/-- The standard chain arrow is the identity matrix after stabilization. -/
def standardArrow {n m : ℕ} (h : n ≤ m) : standard R n ⟶ standard R m :=
  CostructuredArrow.homMk
    { base := AsSmall.up.map (homOfLE h)
      fiber := ULift.up (1 : Matrix.GeneralLinearGroup (Fin m) R) }
    (by apply ULift.ext; exact (one_mul (M := Group R) _).trans (map_one (of R m)))

/-- The cofinal chain of identity structure arrows in the comma category. -/
def standardSequence : ℕ ⥤ Comma R where
  obj := standard R
  map f := standardArrow R (leOfHom f)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- Every comma object reaches a standard stage through an original finite matrix. -/
lemma reaches_standard (a : Comma R) : ∃ n, Nonempty (a ⟶ standard R n) := by
  obtain ⟨k, g, hg⟩ := exists_of R a.hom.down
  let m := max (rank a.left.base) k
  refine ⟨m, ⟨CostructuredArrow.homMk
    { base := AsSmall.up.map (homOfLE (Nat.le_max_left _ _))
      fiber := ULift.up (transition R k m (Nat.le_max_right _ _) g) } ?_⟩⟩
  apply ULift.ext
  change 1 * of R m (transition R k m (Nat.le_max_right _ _) g) = a.hom.down
  exact (one_mul _).trans ((of_transition R _ g).trans hg.symm)

/-- The original comma category is genuinely contractible by an explicit zigzag. -/
theorem comma_contractible : ContractibleSpace (ClassifyingSpace (Comma R)) :=
  CofinalSequence.contractibleSpace (standardSequence R) (reaches_standard R)

/-- The original projection induces an actual homotopy equivalence. -/
def classifyingHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (Telescope R))
      (ClassifyingSpace (stableCategory R)) :=
  TheoremA.contractibleCommaClassifyingHomotopyEquiv (projection R) (fun d => by
    rcases d with ⟨⟨⟩⟩
    exact comma_contractible R)

/-- The forward map is exactly the realization of the original projection. -/
@[simp]
lemma classifyingHomotopyEquiv_toFun :
    (classifyingHomotopyEquiv R).toFun = (classifyingSpaceMap (projection R)).hom := rfl

end StableGeneralLinear.GrothendieckModel
