/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.GroupTheory.StableGeneralLinear.FieldDeterminant
public import Colib.KTheory.Quillen.Field.ElementaryProjectiveKOne
public import Colib.KTheory.Quillen.Field.UpperModuleComparison

/-!
Implementation provenance: `Quillen/KTheory/Field/ModuleDeterminant.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Native mathematical owners replace the
source namespaces; the original comparisons, representatives, and hypotheses are retained.

# The determinant on the actual upper finite-module Q-group

The comparison retains the original stable elementary quotient, completion,
projective Q-group, opposite-ring scalar restriction and upper SmallModel.
Naturality uses literal finite-module tensor extension. The representative
formula here concerns the native completion class. A separate positive matrix-cube
comparison proves that the literal positive capped matrix cube has the ordinary
determinant under this same equivalence.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.ExactCategory
attribute [local instance] Abelian.hasFiniteBiproducts
universe u
open ModuleCat.FiniteProjective.StableCompletion

namespace FGModuleCat

variable (F : Type u) [Field F]

/-- The full canonical stable-quotient comparison to the client's actual module group. -/
def elementaryUpperModuleKOneEquiv : StableGeneralLinear.ElementaryQuotient F ≃*
    (abelianExactStructure (FGModuleCat.{u} F)).SmallK.{u + 1} 1 :=
  (elementaryProjectiveKOneEquiv F).trans (rightProjectiveUpperModuleKEquiv F 1)

/-- The original finite-matrix value is retained through every specified transport. -/
theorem elementaryUpperModuleKOneEquiv_quotientMap (g : StableGeneralLinear.Group F) :
    elementaryUpperModuleKOneEquiv F (StableGeneralLinear.quotientMap F g) =
      rightProjectiveUpperModuleKEquiv F 1
        (zeroCompletionPositiveKEquiv F 0 (stableGroupPiOneMap F g)) := rfl

/-- The canonical comparison commutes with the actual upper-universe tensor K-map. -/
theorem elementaryUpperModuleKOneEquiv_ringMap {L : Type u} [Field L] (f : F →+* L)
    (a : StableGeneralLinear.ElementaryQuotient F) :
    elementaryUpperModuleKOneEquiv L (StableGeneralLinear.quotientRingMap f a) =
      (finiteModuleExtensionExact f).smallKMap.{u + 1} 1
        (elementaryUpperModuleKOneEquiv F a) := by
  change rightProjectiveUpperModuleKEquiv L 1
    (elementaryProjectiveKOneEquiv L (StableGeneralLinear.quotientRingMap f a)) = _
  rw [elementaryProjectiveKOneEquiv_ringMap, rightProjectiveUpperModuleKEquiv_baseChange]
  rfl

/-- The module determinant is the inverse of the canonical composite followed by det. -/
def moduleDetEquiv : (abelianExactStructure (FGModuleCat.{u} F)).SmallK.{u + 1} 1 ≃* Fˣ :=
  (elementaryUpperModuleKOneEquiv F).symm.trans (StableGeneralLinear.quotientDetEquiv F)

/-- Literal scalar-extension naturality on the client's unchanged upper module group. -/
theorem moduleDetEquiv_scalarExtension {L : Type u} [Field L] (f : F →+* L)
    (a : (abelianExactStructure (FGModuleCat.{u} F)).SmallK.{u + 1} 1) :
    moduleDetEquiv L ((finiteModuleExtensionExact f).smallKMap.{u + 1} 1 a) =
      Units.map f.toMonoidHom (moduleDetEquiv F a) := by
  obtain ⟨b, rfl⟩ := (elementaryUpperModuleKOneEquiv F).surjective a
  rw [← elementaryUpperModuleKOneEquiv_ringMap]
  change StableGeneralLinear.quotientDetEquiv L
    ((elementaryUpperModuleKOneEquiv L).symm (elementaryUpperModuleKOneEquiv L _)) =
      Units.map f.toMonoidHom (StableGeneralLinear.quotientDetEquiv F
        ((elementaryUpperModuleKOneEquiv F).symm (elementaryUpperModuleKOneEquiv F b)))
  rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  exact DFunLike.congr_fun (StableGeneralLinear.quotientDetEquiv_naturality F f) b

/-- The same literal scalar-extension square as an equality of group homomorphisms. -/
theorem moduleDetEquiv_scalarExtension_hom {L : Type u} [Field L] (f : F →+* L) :
    (moduleDetEquiv L).toMonoidHom.comp ((finiteModuleExtensionExact f).smallKMap.{u + 1} 1) =
      (Units.map f.toMonoidHom).comp (moduleDetEquiv F).toMonoidHom :=
  MonoidHom.ext (moduleDetEquiv_scalarExtension F f)

/-- The ordinary determinant of a transported native matrix-completion representative. -/
theorem moduleDetEquiv_matrix (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) F) :
    moduleDetEquiv F (rightProjectiveUpperModuleKEquiv F 1
      (zeroCompletionPositiveKEquiv F 0
        (stableGroupPiOneMap F (StableGeneralLinear.of F n g)))) =
      Matrix.GeneralLinearGroup.det g := by
  rw [← elementaryUpperModuleKOneEquiv_quotientMap]
  exact congrArg (StableGeneralLinear.quotientDetEquiv F)
    ((elementaryUpperModuleKOneEquiv F).symm_apply_apply _)

end FGModuleCat
