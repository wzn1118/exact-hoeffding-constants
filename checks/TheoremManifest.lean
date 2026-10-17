import Lean

/-! Export metadata from checked Lean declarations. This audit helper neither
constructs proofs nor changes any mathematical declaration. -/

open Lean Meta

namespace ExactHoeffdingAudit

private def namesJson (names : Array Name) : Json :=
  Json.arr ((names.map Name.toString).qsort (· < ·) |>.map Json.str)

private def rangeJson (range : DeclarationRange) : Json :=
  Json.mkObj [
    ("start_line", toJson range.pos.line),
    ("start_column", toJson range.pos.column),
    ("end_line", toJson range.endPos.line),
    ("end_column", toJson range.endPos.column)]

/-- Export actual theorem types, direct expression dependencies, and transitive
axioms. A missing declaration or a definition in place of a theorem is an error. -/
def exportTheoremManifest (requested : Array String) (output : String) : MetaM Unit := do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for requestedName in requested do
    let name := requestedName.toName
    let some info := env.find? name
      | throwError "manifest: missing Lean declaration {name}"
    let .thmInfo theoremInfo := info
      | throwError "manifest: declaration {name} is not a theorem"
    let typeText ← withOptions (fun options =>
      options.setBool `pp.fullNames true |>.setBool `pp.universes true
        |>.setBool `pp.explicit true |>.setBool `pp.proofs true
        |>.setBool `pp.deepTerms true |>.set `pp.maxSteps (10000000 : Nat)
        |>.set `pp.width (120 : Nat)) do
      return (← ppExpr theoremInfo.type).pretty 120
    let moduleName := match env.getModuleIdxFor? name with
      | some index => env.header.moduleNames[index]!.toString
      | none => env.mainModule.toString
    let declarationRange ← findDeclarationRanges? name
    let axioms ← collectAxioms name
    rows := rows.push (Json.mkObj [
      ("name", Json.str name.toString),
      ("kind", Json.str "theorem"),
      ("module", Json.str moduleName),
      ("universe_parameters", toJson (theoremInfo.levelParams.map Name.toString)),
      ("type_pretty", Json.str typeText),
      ("type_expression", Json.str (reprStr theoremInfo.type)),
      ("proof_expression_hash64", Json.str (toString theoremInfo.value.hash)),
      ("type_dependencies", namesJson theoremInfo.type.getUsedConstants),
      ("proof_direct_dependencies", namesJson theoremInfo.value.getUsedConstants),
      ("axioms", namesJson axioms),
      ("lean_source_range", match declarationRange with
        | some ranges => rangeJson ranges.range
        | none => Json.null)])
  let document := Json.mkObj [
    ("lean_version", Json.str Lean.versionString),
    ("declarations", Json.arr rows)]
  IO.FS.writeFile output (document.pretty ++ "\n")

end ExactHoeffdingAudit
