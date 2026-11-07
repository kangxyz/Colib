/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.Adjunction
public import Colib.Topology.ClassifyingSpace.Contraction

/-!
# Contracting a thin category with a cofinal sequence

For a thin category with a cofinal natural-number chain, the least reachable
chain index defines an actual endofunctor. There are natural transformations
from both the identity and the constant first-chain-object functor to this
endofunctor. Realizing this explicit zigzag proves genuine contractibility,
without passing from weak contractibility to contractibility.

Implementation provenance: `Quillen/Topology/ClassifyingSpace/CofinalSequence.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps and universes are retained.
-/
@[expose] public section

noncomputable section

universe u v
open CategoryTheory

namespace CategoryTheory.CofinalSequence

variable {C : Type u} [Category.{v} C] [Quiver.IsThin C]
    (F : ℕ ⥤ C) (h : ∀ c : C, ∃ n, Nonempty (c ⟶ F.obj n))

/-- The least member of the specified chain reachable from an object. -/
def bound (c : C) : ℕ := by
  classical
  exact Nat.find (h c)

/-- The original arrow to the least reachable chain member. -/
def toBound (c : C) : c ⟶ F.obj (bound F h c) := by
  classical
  exact (Nat.find_spec (h c)).some

omit [Quiver.IsThin C] in
lemma bound_mono {c d : C} (f : c ⟶ d) : bound F h c ≤ bound F h d :=
  by
    classical
    exact Nat.find_min' (h c) ⟨f ≫ toBound F h d⟩

/-- The endofunctor moving each object to its least reachable chain member. -/
def raiseFunctor : C ⥤ C where
  obj c := F.obj (bound F h c)
  map f := F.map (homOfLE (bound_mono F h f))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The original cofinality arrows form a natural transformation. -/
def identityToRaise : 𝟭 C ⟶ raiseFunctor F h where
  app c := toBound F h c
  naturality _ _ _ := Subsingleton.elim _ _

/-- The first chain object maps naturally to every raised object. -/
def constantToRaise : (Functor.const C).obj (F.obj 0) ⟶ raiseFunctor F h where
  app c := F.map (homOfLE (Nat.zero_le (bound F h c)))
  naturality _ _ _ := Subsingleton.elim _ _

/-- The realized identity-to-raise-to-constant zigzag, as an actual homotopy. -/
def contraction :
    (ContinuousMap.id (ClassifyingSpace C)).Homotopy
      (ContinuousMap.const _ (classifyingSpacePoint (F.obj 0))) := by
  have h₁ := classifyingSpaceNaturalTransformationHomotopy (identityToRaise F h)
  have h₂ := classifyingSpaceNaturalTransformationHomotopy (constantToRaise F h)
  simpa only [classifyingSpaceMap_id, TopCat.hom_id, classifyingSpaceMap_const] using
    h₁.trans h₂.symm

include F h in
/-- The explicit cofinal-sequence zigzag contracts the actual classifying space. -/
theorem contractibleSpace : ContractibleSpace (ClassifyingSpace C) := by
  apply (contractible_iff_id_nullhomotopic _).2
  refine ⟨classifyingSpacePoint (F.obj 0), ?_⟩
  exact ⟨contraction F h⟩

end CategoryTheory.CofinalSequence
