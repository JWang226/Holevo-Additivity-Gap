/-
Copyright (c) 2026 Free Entropy formalization contributors.
Original QMDL attribution/licensing: https://github.com/JWang226/QMDL/blob/fd36df94068299e3d5e0bb193d19649319a40422/NOTICE
Copyright (c) 2026 the Nonadditivity project contributors (adaptations).
See COPYRIGHT.md for this project’s attribution and licensing status.
Adaptation: Adapted for Holevo-Additivity-Gap from JWang226/QMDL at fd36df94068299e3d5e0bb193d19649319a40422; original attribution retained.
-/
import Comparator
import Lean4Checker.Replay
import Export.Parse

/-! Local diagnostic only. This uses the pinned Comparator comparison and axiom
checker, then replays the exported proof in Lean's kernel. It does not sandbox
the build or exporter. No sandboxed upstream CLI execution is claimed. -/

private structure DiagnosticConfig where
  challenge_module : String
  solution_module : String
  theorem_names : Array String
  permitted_axioms : Array String
  enable_nanoda : Bool
  deriving Lean.FromJson

private def primitiveTargets : Array Lean.Name := #[
  ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow, ``Nat.gcd, ``Nat.div,
  ``Nat.mod, ``Nat.beq, ``Nat.ble, ``Nat.land, ``Nat.lor, ``Nat.xor,
  ``Nat.shiftLeft, ``Nat.shiftRight, ``String.ofList
]

private def readExport (path : String) : IO Export.ExportedEnv :=
  IO.FS.withFile path .read fun handle =>
    Export.parseStream (IO.FS.Stream.ofHandle handle)

def main (args : List String) : IO Unit := do
  let [configPath, challengePath, solutionPath] := args
    | throw <| .userError "Expected CONFIG CHALLENGE_EXPORT SOLUTION_EXPORT"
  let config : DiagnosticConfig ← IO.ofExcept <| Lean.FromJson.fromJson? <|
    ← IO.ofExcept <| Lean.Json.parse (← IO.FS.readFile configPath)
  if config.enable_nanoda then
    throw <| .userError "This local diagnostic does not run nanoda."
  IO.println "UNSANDBOXED diagnostic: parsing exports. Nanoda is disabled."
  let challenge ← readExport challengePath
  let solution ← readExport solutionPath
  let theoremNames := config.theorem_names.map String.toName
  let axioms := config.permitted_axioms.map String.toName
  IO.ofExcept <| Comparator.compareAt challenge solution (theoremNames ++ axioms)
    primitiveTargets
  IO.println "Pinned Comparator: statements and referenced constants match."
  IO.ofExcept <| Comparator.checkAxioms solution theoremNames axioms
  IO.println "Pinned Comparator: solution axiom closure accepted."
  let env ← Lean.mkEmptyEnvironment
  let constMap := solution.constMap.erase `Quot.mk |>.erase `Quot.lift |>.erase `Quot.ind
  discard <| env.replay' constMap
  IO.println "Lean kernel replay accepted. UNSANDBOXED diagnostic only."
