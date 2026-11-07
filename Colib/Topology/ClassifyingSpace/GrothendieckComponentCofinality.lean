/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Grothendieck.GroupoidRightFactors
public import Colib.Topology.ClassifyingSpace.CofinalSequence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
Adapted from `Quillen/Topology/ClassifyingSpace/GrothendieckComponentCofinality.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual objects,
functors, coefficient universes and comparison maps.

# Actual cofinal sequences in groupoid-telescope comma categories -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace CategoryTheory.Grothendieck
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable (F : ℕ ⥤ Cat.{u, u}) [∀ n, IsGroupoid (F.obj n)]
  {D : Type u} [Category.{u} D] (G : D ⥤ Grothendieck F) [G.Full] [G.Faithful]

/-- Original comma arrows are unique because their structure arrows are epic
and the specified source functor is faithful. -/
instance structuredArrow_thin (x : Grothendieck F) : Quiver.IsThin (StructuredArrow x G) := by
  intro a b
  constructor
  intro f g
  apply StructuredArrow.hom_ext
  apply G.map_injective
  apply (cancel_epi a.hom).mp
  exact (StructuredArrow.w f).trans (StructuredArrow.w g).symm

variable (S : ℕ ⥤ D) (hS : ∀ n, (G.obj (S.obj n)).base = n)
  (x : Grothendieck F) (k : ℕ) (f : x ⟶ G.obj (S.obj k))

/-- The original arrow to one stage extends along the specified sequence. -/
def commaSequenceObject (n : ℕ) : StructuredArrow x G :=
  StructuredArrow.mk (f ≫ G.map (S.map (homOfLE (Nat.le_add_right k n))))

/-- The actual shifted sequence of structure arrows in the comma category. -/
def commaSequence : ℕ ⥤ StructuredArrow x G where
  obj := commaSequenceObject F G S x k f
  map {n m} h := StructuredArrow.homMk (S.map (homOfLE (Nat.add_le_add_left (leOfHom h) k))) (by
    dsimp [commaSequenceObject]
    rw [Category.assoc, ← G.map_comp, ← S.map_comp]
    congr 2)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

include hS in
/-- Every comma object factors into the original shifted sequence. -/
theorem reaches_commaSequence (a : StructuredArrow x G) :
    ∃ n, Nonempty (a ⟶ (commaSequence F G S x k f).obj n) := by
  let n := (G.obj a.right).base
  let b := commaSequenceObject F G S x k f n
  have hstage : (G.obj a.right).base ≤ (G.obj b.right).base := by
    change n ≤ (G.obj (S.obj (k + n))).base
    rw [hS]
    omega
  let g := rightFactor F a.hom b.hom hstage
  refine ⟨n, ⟨StructuredArrow.homMk (G.preimage g) ?_⟩⟩
  rw [G.map_preimage]
  exact rightFactor_fac F a.hom b.hom hstage

include S hS k f in
/-- A reachable original stage contracts the entire actual comma category. -/
theorem structuredArrow_contractible_of_reaches :
    ContractibleSpace (ClassifyingSpace (StructuredArrow x G)) :=
  CofinalSequence.contractibleSpace (commaSequence F G S x k f)
    (reaches_commaSequence F G S hS x k f)

/-- Every object in the component of an original stage-zero vertex reaches
some original stage of the specified sequence. -/
theorem reaches_sequence_of_zigzag (P : ℕ ⥤ Grothendieck F)
    (hP : ∀ n, (P.obj n).base = n) {y : Grothendieck F}
    (hy : Zigzag (P.obj 0) y) : ∃ n, Nonempty (y ⟶ P.obj n) := by
  induction hy with
  | refl => exact ⟨0, ⟨𝟙 _⟩⟩
  | @tail y z hy hz ih =>
    obtain ⟨n, ⟨g⟩⟩ := ih
    rcases hz with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
    · let m := max n z.base
      let g' := g ≫ P.map (homOfLE (Nat.le_max_left n z.base))
      refine ⟨m, ⟨rightFactor F f g' ?_⟩⟩
      rw [hP]
      exact Nat.le_max_right n z.base
    · exact ⟨n, ⟨f ≫ g⟩⟩

end CategoryTheory.Grothendieck
