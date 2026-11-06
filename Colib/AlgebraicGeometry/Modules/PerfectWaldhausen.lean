/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Complexes
public import Colib.CategoryTheory.Waldhausen.CofibrationClosedSubcategory
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.MappingCone
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RepresentativeIndependence
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-!
# The actual monomorphism/quasi-isomorphism Waldhausen structure on perfect complexes

Native Stacks perfectness is closed under actual pushouts along monomorphisms. The cone of
an injection in a short exact sequence is quasi-isomorphic to its actual quotient, so that
quotient is perfect when the first two complexes are. The pushout short exact sequence then
reduces pushout closure to finite direct sums and this quotient statement.

The inherited structure retains the ambient zero complex, ambient monomorphisms and genuine
quasi-isomorphisms. No derived localization is used as the underlying category, and no
K-theory invariance statement is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry StrictlyPerfect
open scoped ZeroObject

namespace AlgebraicGeometry.RingedSpace

universe u

variable {X : RingedSpace.{u, u}}

/-- The actual quotient in a short exact sequence is perfect when its first two complexes are. -/
@[stacks 08CR "Third-vertex specialization to a short exact sequence and its actual quotient"]
theorem isPerfectComplex_X₃_of_shortExact
    {S : ShortComplex (CochainComplex (OXMod.{u, u, u} X) ℤ)} (hS : S.ShortExact)
    (h₁ : IsPerfectComplex S.X₁) (h₂ : IsPerfectComplex S.X₂) :
    IsPerfectComplex S.X₃ :=
  (isPerfectComplex_mappingCone S.f h₁ h₂).of_quasiIso
    (CochainComplex.mappingCone.descShortComplex S)
    (CochainComplex.mappingCone.quasiIso_descShortComplex hS)

private theorem isPerfectComplex_biprod {A B : CochainComplex (OXMod.{u, u, u} X) ℤ}
    (hA : IsPerfectComplex A) (hB : IsPerfectComplex B) : IsPerfectComplex (A ⊞ B) := by
  let : HasDerivedCategory.{u + 1} (OXMod.{u, u, u} X) := HasDerivedCategory.standard _
  let S : ShortComplex (CochainComplex (OXMod.{u, u, u} X) ℤ) :=
    ShortComplex.mk (biprod.inl : A ⟶ A ⊞ B) (biprod.snd : A ⊞ B ⟶ B) (by simp)
  have hS : S.ShortExact := (ShortComplex.Splitting.ofHasBinaryBiproduct A B).shortExact
  have h : IsPerfect (DerivedCategory.Q.obj (A ⊞ B)) :=
    Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₂_of_distinguished
      (DerivedCategory.triangleOfSES hS) (DerivedCategory.triangleOfSES_distinguished hS)
      hA.isPerfect hB.isPerfect
  exact isPerfectComplex_of_isPerfect_representation h ⟨Iso.refl _⟩

/-- Every displayed pushout along a monomorphism of perfect complexes has perfect apex. -/
theorem isPerfectComplex_of_isPushout
    {A B D Q : CochainComplex (OXMod.{u, u, u} X) ℤ}
    {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ Q} {j : D ⟶ Q} [Mono i]
    (h : IsPushout i f g j) (hA : IsPerfectComplex A)
    (hB : IsPerfectComplex B) (hD : IsPerfectComplex D) : IsPerfectComplex Q := by
  have hs : h.shortComplex.ShortExact :=
    { exact := h.exact_shortComplex
      mono_f := by dsimp [CommSq.shortComplex]; infer_instance
      epi_g := h.epi_shortComplex_g }
  exact isPerfectComplex_X₃_of_shortExact hs hA (isPerfectComplex_biprod hB hD)

/-- Native perfectness contains the actual ambient zero and every relevant ambient pushout. -/
theorem perfectComplexes_cofibrationClosed (X : RingedSpace.{u, u}) :
    Waldhausen.CofibrationClosedSubcategory.Closed
      (Waldhausen.complexes (OXMod.{u, u, u} X)) (IsPerfectComplex (X := X)) where
  zero_mem := isPerfectComplex_of_forall_isZero fun n =>
    (HomologicalComplex.eval _ _ n).map_isZero (isZero_zero _)
  pushout_mem hi h hA hB hD := by
    have : Mono _ := hi
    exact isPerfectComplex_of_isPushout h hA hB hD

/-- The genuine full-chain-complex Waldhausen structure with ambient monomorphisms and
quasi-isomorphisms, retaining the ambient zero and actual pushouts. -/
def perfectComplexesWaldhausen (X : RingedSpace.{u, u}) :
    Waldhausen.Structure (ObjectProperty.FullSubcategory (IsPerfectComplex (X := X))) :=
  Waldhausen.CofibrationClosedSubcategory.waldhausenStructure
    (Waldhausen.complexes (OXMod.{u, u, u} X)) (IsPerfectComplex (X := X))
    (perfectComplexes_cofibrationClosed X)

end AlgebraicGeometry.RingedSpace

attribute [colib_tag "COL-0178",
  colib_ref "Waldhausen1985" "Sections 1.1-1.2, pp.320-321 and 326-327"
    "background" "The full-chain-complex structure inherits ambient monomorphisms \
    and quasi-isomorphisms"]
  AlgebraicGeometry.RingedSpace.isPerfectComplex_X₃_of_shortExact
  AlgebraicGeometry.RingedSpace.isPerfectComplex_of_isPushout
  AlgebraicGeometry.RingedSpace.perfectComplexes_cofibrationClosed
  AlgebraicGeometry.RingedSpace.perfectComplexesWaldhausen

attribute [colib_ref "quillen" "Quillen/AlgebraicGeometry/PerfectComplexes/KTheory.lean:53-55"
  "adaptation" "The structure is constructed directly on native Stacks perfect complexes"]
  AlgebraicGeometry.RingedSpace.perfectComplexesWaldhausen
