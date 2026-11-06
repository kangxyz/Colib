/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.AmbientValue

/-!
# Path Value

The geometric input for global descent is an open cover of the entire space.
-/

@[expose] public section

noncomputable section
open Set CategoryTheory
universe u v w z
namespace FundamentalGroupoid.OpenCover
variable {X : Type u} [TopologicalSpace X] {ι : Type v} {U : ι → Set X}
variable {C : Type w} [Category.{z} C]

/-- The geometric input for global descent is an open cover of the entire space. -/
structure CoverData (U : ι → Set X) where
  isOpen : ∀ i, IsOpen (U i)
  covers : ∀ x, x ∈ ⋃ i, U i

namespace CoverData
variable (c : CoverData U)

/-- Choose a finite subdivision subordinate to the given open cover. -/
def subdivision {x y : X} (p : Path x y) : PathSubdivision (U := U) p :=
  Classical.choice (pathSubdivision_nonempty p U c.isOpen (fun _ _ => c.covers _))

end CoverData
namespace ChartData
variable (d : ChartData (C := C) U) (c : CoverData U)

/-- Choose a finite subordinate subdivision and take its actual ordered value. -/
def pathValue {x y : X} (p : Path x y) : d.obj x ⟶ d.obj y :=
  (c.subdivision p).value d

theorem pathValue_eq (hc : d.Compatible) {x y : X} (p : Path x y)
    (s : PathSubdivision (U := U) p) : d.pathValue c p = s.value d :=
  (c.subdivision p).value_eq s d hc (fun _ _ => c.covers _)

/-- The chosen global path value recovers every applicable original chart value. -/
theorem pathValue_local (hc : d.Compatible) (i : ι) {x y : X}
    (p : Path x y) (hp : Set.range p ⊆ U i) :
    d.pathValue c p = d.localValue i p hp :=
  (c.subdivision p).value_eq_localValue d hc i hp

/-- The chosen global path value is constant on actual ambient homotopy classes. -/
theorem pathValue_homotopy (hc : d.Compatible) {x y : X} {p q : Path x y}
    (H : p.Homotopy q) : d.pathValue c p = d.pathValue c q :=
  (c.subdivision p).value_eq_of_homotopy (c.subdivision q) H d hc c.isOpen
    (fun _ _ => c.covers _)

theorem pathValue_refl (hc : d.Compatible) (x : X) :
    d.pathValue c (Path.refl x) = 𝟙 (d.obj x) := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (c.covers x)
  have hp : Set.range (Path.refl x) ⊆ U i := by rintro _ ⟨t, rfl⟩; exact hi
  rw [d.pathValue_local c hc i _ hp, d.localValue_refl]

/-- Descent to the actual homotopy quotient. This is a map on hom sets; functorial
composition is a separate theorem and is not an assumption of this definition. -/
def quotientValue (hc : d.Compatible) {x y : X} :
    Path.Homotopic.Quotient x y → (d.obj x ⟶ d.obj y) :=
  _root_.Quotient.lift (d.pathValue c) (by
    intro p q h
    obtain ⟨H⟩ := h
    exact d.pathValue_homotopy c hc H)

@[simp]
theorem quotientValue_mk (hc : d.Compatible) {x y : X} (p : Path x y) :
    d.quotientValue c hc (Path.Homotopic.Quotient.mk p) = d.pathValue c p := rfl

end ChartData
end FundamentalGroupoid.OpenCover
