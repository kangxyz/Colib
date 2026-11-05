/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Lean

open Lean in
/-- Read catalog declarations and signatures from the built Colib environment. -/
unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  withImportModules #[{ module := `Colib }] {} fun env => do
    let action : MetaM Json := do
      let mut rows := #[]
      for argument in args do
        let name := argument.toName
        let some info := env.find? name
          | throwError "Unknown catalog declaration {name}"
        let some index := env.getModuleIdxFor? name
          | throwError "No defining module for {name}"
        let type ← Meta.ppExpr info.type
        rows := rows.push <| Json.mkObj [
          ("name", toJson argument),
          ("module", toJson (env.header.moduleNames[index]!).toString),
          ("type", toJson type.pretty)]
      return Json.arr rows
    let (result, _, _) ← action.toIO { fileName := "<colib-catalog>", fileMap := default }
      { env }
    IO.println result.compress
