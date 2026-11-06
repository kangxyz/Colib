/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Abelian.Devissage.Layers
public import Mathlib.CategoryTheory.Abelian.CommSq

/-!
# Actual quotient maps of nested subobjects and layers

Quotienting a monomorphism by a common source preserves monicity and gives the
original pullback square. The intermediate quotient of an ordered pair of
layers retains its actual mono and epi maps. No Q object is constructed here.


## Implementation provenance

Adapted from
`Quillen/Aglib/CategoryTheory/ExactCategory/Filtration/LayerQuotients.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps and independent object/hom universes
are retained. No extension-closure assumption or Resolution structure is used.
The source `Quillen.Devissage` namespace is now
`CategoryTheory.Abelian.Devissage`; no K-theory dependency is introduced.
-/
@[expose] public section

open CategoryTheory.ObjectProperty

noncomputable section
universe v u
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
namespace CategoryTheory.Abelian.Devissage
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Passing to quotients by the same subobject gives a monomorphism. -/
lemma quotientMap_mono {A U V : C} (i : A ⟶ U) (g : U ⟶ V) (k : A ⟶ V)
    [Mono g] (w : i ≫ g = k) :
    Mono (cokernel.map i k (𝟙 A) g (by simpa using w)) := by
  apply Abelian.mono_cokernel_map_of_isPullback
  exact IsPullback.of_vert_isIso_mono ⟨by simpa using w⟩

/-- The quotient square of an inclusion of subobjects is a pullback. -/
lemma quotientMap_isPullback {A U V : C} (i : A ⟶ U) (g : U ⟶ V) (k : A ⟶ V)
    [Mono g] (w : i ≫ g = k) :
    IsPullback (cokernel.π i) g
      (cokernel.map i k (𝟙 A) g (by simpa using w)) (cokernel.π k) := by
  let m := cokernel.map i k (𝟙 A) g (by simpa using w)
  let : Mono m := quotientMap_mono i g k w
  have wk : k ≫ cokernel.π g = 0 := by rw [← w, assoc, cokernel.condition, comp_zero]
  let d := cokernel.desc k (cokernel.π g) wk
  have md : m ≫ d = 0 := by
    apply (cancel_epi (cokernel.π i)).mp
    simp [m, d]
  have hz (s : PullbackCone m (cokernel.π k)) : s.snd ≫ cokernel.π g = 0 := by
    rw [← cokernel.π_desc k (cokernel.π g) wk, ← assoc, ← s.condition, assoc, md, comp_zero]
  apply IsPullback.of_isLimit (c := PullbackCone.mk (cokernel.π i) g (by simp))
  apply PullbackCone.IsLimit.mk (by simp [m])
    (fun s => Abelian.monoLift g s.snd (hz s))
  · intro s
    apply (cancel_mono m).mp
    simpa [m] using s.condition.symm
  · intro s
    exact Abelian.monoLift_comp _ _ _
  · intro s a _ ha
    apply (cancel_mono g).mp
    simpa using ha

variable (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderSubobjects]
  [P.IsClosedUnderQuotients] [P.IsClosedUnderFiniteProducts] (M : C)

namespace Layer
variable {P M}

/-- The intermediate quotient for an inclusion of layers. -/
abbrev middle {L K : Layer P M} (h : L ≤ K) : C :=
  cokernel (Subobject.ofLE K.lower L.upper (h.1.trans L.le))

/-- The intermediate quotient embeds in the target quotient. -/
def rightMap {L K : Layer P M} (h : L ≤ K) : middle h ⟶ K.quotient :=
  cokernel.map (Subobject.ofLE K.lower L.upper (h.1.trans L.le))
    (Subobject.ofLE K.lower K.upper K.le) (𝟙 _)
    (Subobject.ofLE L.upper K.upper h.2) (by simp)

instance rightMap_mono {L K : Layer P M} (h : L ≤ K) : Mono (rightMap h) :=
  quotientMap_mono _ _ _ (by simp)

/-- The intermediate quotient surjects onto the source quotient. -/
def leftMap {L K : Layer P M} (h : L ≤ K) : middle h ⟶ L.quotient :=
  cokernel.desc _ (cokernel.π (Subobject.ofLE L.lower L.upper L.le)) (by
    rw [← Subobject.ofLE_comp_ofLE K.lower L.lower L.upper h.1 L.le, assoc]
    simp)

instance leftMap_epi {L K : Layer P M} (h : L ≤ K) : Epi (leftMap h) :=
  epi_of_epi_fac (cokernel.π_desc _ _ _)

end Layer
end CategoryTheory.Abelian.Devissage
