/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public meta import Mathlib.Tactic.CrossRefAttribute

/-!
# Colib Library identifiers and literature references

`@[colib_tag "COL-0004"]` binds a declaration to a permanent mathematical item.
`@[colib_ref "WeibelKBook" "II, section 2" "adaptation" "field case"]` records
an exact book or paper locator and its correspondence scope. Stacks references use the
existing `@[stacks]` attribute. Bibliographic keys are validated by the Library exporter.
-/

public meta section

open Lean Elab

namespace Colib.Library

/-- A declaration registered under a permanent Library identifier. -/
structure Binding where
  /-- The declaration's fully qualified name. -/
  declName : Name
  /-- The permanent mathematical item identifier. -/
  id : String
  deriving BEq, Inhabited

/-- A declaration's precise reference to a bibliographic source. -/
structure Citation where
  /-- The declaration carrying the reference. -/
  declName : Name
  /-- The key in the maintained bibliography. -/
  source : String
  /-- The theorem, definition, section or equation locator. -/
  locator : String
  /-- How the declaration corresponds to the source. -/
  relation : String
  /-- The particular clause, hypotheses or map conventions covered. -/
  scope : String
  deriving BEq, Inhabited

/-- Persistent Library membership, read by native export tools. -/
initialize bindingExt : SimplePersistentEnvExtension Binding (Array (Array Binding)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries
    addEntryFn := fun entries _ => entries
  }

/-- Persistent bibliographic references, read by native export tools. -/
initialize citationExt : SimplePersistentEnvExtension Citation (Array (Array Citation)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries
    addEntryFn := fun entries _ => entries
  }

/-- All permanent-item bindings visible in an environment. -/
def bindings (env : Environment) : Array Binding :=
  let state := PersistentEnvExtension.getState bindingExt env
  state.2.flatten ++ state.1.toArray.reverse

/-- All book and paper citations visible in an environment. -/
def citations (env : Environment) : Array Citation :=
  let state := PersistentEnvExtension.getState citationExt env
  state.2.flatten ++ state.1.toArray.reverse

/-- Attribute syntax for a permanent mathematical item. -/
syntax (name := colibTagAttr) "colib_tag " str : attr

/-- Attribute syntax for an exact bibliographic locator and correspondence scope. -/
syntax (name := colibRefAttr) "colib_ref " str ppSpace str ppSpace str ppSpace str : attr

initialize registerBuiltinAttribute {
  name := `colibTagAttr
  descr := "Register a declaration as an implementation of a Colib Library item."
  applicationTime := .afterTypeChecking
  add := fun decl stx _ => do
    let `(attr| colib_tag $id:str) := stx | throwUnsupportedSyntax
    let id := id.getString
    unless id.startsWith "COL-" && id.length ≥ 8 &&
        (id.drop 4).toString.toList.all Char.isDigit do
      throwError "Expected a permanent COL identifier with at least four digits"
    let entry : Binding := ⟨decl, id⟩
    modifyEnv (bindingExt.addEntry · entry)
}

initialize registerBuiltinAttribute {
  name := `colibRefAttr
  descr := "Record an exact book or paper reference for a declaration."
  applicationTime := .afterTypeChecking
  add := fun decl stx _ => do
    let `(attr| colib_ref $source:str $locator:str $relation:str $scope:str) := stx
      | throwUnsupportedSyntax
    let source := source.getString
    let locator := locator.getString
    let relation := relation.getString
    let scope := scope.getString
    unless [source, locator, scope].all (fun value => !value.trimAscii.toString.isEmpty) do
      throwError "A literature reference needs a key, exact locator and correspondence scope"
    unless ["whole", "clause", "specialization", "generalization", "adaptation", "comparison",
        "ingredient", "background"].contains relation do
      throwError "Unknown literature correspondence relation {relation}"
    let entry : Citation := ⟨decl, source, locator, relation, scope⟩
    modifyEnv (citationExt.addEntry · entry)
}

end Colib.Library
