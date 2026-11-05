/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Colib
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let bindings := Colib.Library.bindings env
  let allCitations := Colib.Library.citations env
  let mut names := bindings.foldl (fun names binding => names.insert binding.declName) NameSet.empty
  for citation in allCitations do
    names := names.insert citation.declName
  let stacksState := PersistentEnvExtension.getState Mathlib.CrossRef.tagExt env
  let allStacks := stacksState.2.flatten ++ stacksState.1.toArray.reverse
  for tag in allStacks do
    if tag.database == .stacks then
      if let some index := env.getModuleIdxFor? tag.declName then
        if (env.header.moduleNames[index]!).getRoot == `Colib then
          names := names.insert tag.declName
  let mut declarations := #[]
  for name in names.toList do
    let some info := env.find? name | throwError "Unknown Library declaration {name}"
    let some index := env.getModuleIdxFor? name | throwError "No defining module for {name}"
    let type ← liftTermElabM (Meta.ppExpr info.type)
    let used := info.getUsedConstantsAsSet
    declarations := declarations.push <| Json.mkObj [
      ("name", toJson name.toString),
      ("module", toJson (env.header.moduleNames[index]!).toString),
      ("type", toJson type.pretty),
      ("dependencies", toJson (used.toList.map Name.toString))]
  let registeredModules := names.toList.foldl (fun modules name =>
    match env.getModuleIdxFor? name with
    | some index => modules.insert (env.header.moduleNames[index]!)
    | none => modules) NameSet.empty
  let mut modules := #[]
  for index in [:env.header.moduleNames.size] do
    let name := env.header.moduleNames[index]!
    if name.getRoot == `Colib || registeredModules.contains name then
      modules := modules.push <| Json.mkObj [
        ("name", toJson name.toString),
        ("imports", toJson ((env.header.moduleData[index]!).imports.map
          (fun imported => imported.module.toString)))]
  let itemBindings := bindings.map fun binding => Json.mkObj [
    ("name", toJson binding.declName.toString), ("id", toJson binding.id)]
  let citations := allCitations.filterMap fun citation =>
    if names.contains citation.declName then some <| Json.mkObj [
      ("name", toJson citation.declName.toString),
      ("source", toJson citation.source), ("locator", toJson citation.locator),
      ("relation", toJson citation.relation), ("scope", toJson citation.scope)]
    else none
  let stacksRefs := allStacks.filterMap fun tag =>
    if tag.database == .stacks && names.contains tag.declName then some <| Json.mkObj [
      ("name", toJson tag.declName.toString), ("tag", toJson tag.tag),
      ("scope", toJson tag.comment)]
    else none
  IO.println <| (Json.mkObj [
    ("bindings", Json.arr itemBindings), ("citations", Json.arr citations),
    ("stacks", Json.arr stacksRefs), ("declarations", Json.arr declarations),
    ("modules", Json.arr modules)]).compress
