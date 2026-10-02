/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/
import All
import Lean
import Lean.Util.ForEachExpr
import Lean.Util.ReplaceExpr

/-! Export actual audited constants and compact kernel type expression DAGs.
Only kernel-semantically irrelevant Expr.mdata annotations are omitted. -/
open Lean Elab Command
namespace DeclarationExport
def isProject (n : Name) : Bool :=
  (`Nonadditivity).isPrefixOf n && n != `Nonadditivity ||
    (`_private.Nonadditivity).isPrefixOf n && n != `_private.Nonadditivity
def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
def references (e : Expr) : IO (Array Name) := do
  let found ← IO.mkRef ({} : NameHashSet)
  e.forEach fun t => do
    match t with
    | .const n _ | .proj n _ _ => found.modify (·.insert n)
    | _ => pure ()
  return (← found.get).toArray.qsort (fun a b => a.toString < b.toString)
def tagged (t : String) (xs : Array Json := #[]) : Json := Json.arr (#[toJson t] ++ xs)
def parts : Name → List Json
  | .anonymous => []
  | .str p s => parts p ++ [tagged "str" #[toJson s]]
  | .num p n => parts p ++ [tagged "num" #[toJson (toString n)]]
structure DAGState where
  names : Array Json := #[]
  nameIndex : Std.HashMap Name Nat := {}
  levels : Array Json := #[]
  levelIndex : Std.HashMap Level Nat := {}
  nodes : Array Json := #[]
  exprIndex : Std.HashMap ExprStructEq Nat := {}
  canonicalIndex : Std.HashMap String Nat := {}
abbrev DAGM := StateT DAGState IO
def putName (n : Name) : DAGM Nat := do
  if let some i := (← get).nameIndex[n]? then return i
  let i := (← get).names.size
  modify fun s => {s with names := s.names.push (toJson (parts n)), nameIndex := s.nameIndex.insert n i}
  return i
partial def putLevel (l : Level) : DAGM Nat := do
  if let some i := (← get).levelIndex[l]? then return i
  let node : Json ← match l with
    | .zero => pure (tagged "zero")
    | .succ a => do pure <| tagged "succ" #[toJson (← putLevel a)]
    | .max a b => do pure <| tagged "max" #[toJson (← putLevel a), toJson (← putLevel b)]
    | .imax a b => do pure <| tagged "imax" #[toJson (← putLevel a), toJson (← putLevel b)]
    | .param n => do pure <| tagged "param" #[toJson (← putName n)]
    | .mvar _ => throw (IO.userError "Universe metavariable in compiled type")
  let i := (← get).levels.size
  modify fun s => {s with levels := s.levels.push node, levelIndex := s.levelIndex.insert l i}
  return i
def binder : BinderInfo → String
  | .default => "default" | .implicit => "implicit"
  | .strictImplicit => "strictImplicit" | .instImplicit => "instImplicit"
partial def putExpr (e : Expr) : DAGM Nat := do
  if let some i := (← get).exprIndex[ExprStructEq.mk e]? then return i
  if let .mdata _ child := e then
    let i ← putExpr child
    modify fun s => {s with exprIndex := s.exprIndex.insert (ExprStructEq.mk e) i}
    return i
  let node : Json ← match e with
    | .bvar i => pure (tagged "bvar" #[toJson i])
    | .sort l => do pure <| tagged "sort" #[toJson (← putLevel l)]
    | .const n ls =>
      let ni ← putName n
      let ids ← ls.mapM putLevel
      pure (tagged "const" #[toJson ni, toJson ids])
    | .app f a => do pure <| tagged "app" #[toJson (← putExpr f), toJson (← putExpr a)]
    | .lam n t b bi => do pure <| tagged "lam" #[toJson (← putName n), toJson (← putExpr t), toJson (← putExpr b), toJson (binder bi)]
    | .forallE n t b bi => do pure <| tagged "forall" #[toJson (← putName n), toJson (← putExpr t), toJson (← putExpr b), toJson (binder bi)]
    | .letE n t v b nondep => do pure <| tagged "let" #[toJson (← putName n), toJson (← putExpr t), toJson (← putExpr v), toJson (← putExpr b), toJson nondep]
    | .lit (.natVal n) => pure (tagged "lit_nat" #[toJson (toString n)])
    | .lit (.strVal s) => pure (tagged "lit_string" #[toJson s])
    | .proj n i b => do pure <| tagged "proj" #[toJson (← putName n), toJson i, toJson (← putExpr b)]
    | .fvar _ => throw (IO.userError "Free variable in compiled type")
    | .mvar _ => throw (IO.userError "Expression metavariable in compiled type")
    | .mdata _ _ => throw (IO.userError "Unreachable metadata branch")
  let key := node.compress
  let i ← if let some i := (← get).canonicalIndex[key]? then pure i else do
    let i := (← get).nodes.size
    modify fun s => {s with nodes := s.nodes.push node, canonicalIndex := s.canonicalIndex.insert key i}
    pure i
  modify fun s => {s with exprIndex := s.exprIndex.insert (ExprStructEq.mk e) i}
  return i
def tableValue (table : Array α) (j : Json) : Except String α := do
  let i ← j.getNat?
  match table[i]? with
  | some value => pure value
  | none => throw s!"Invalid DAG table reference {i}"
def decimal (j : Json) : Except String Nat := do
  let value ← j.getStr?
  match value.toNat? with
  | some n => pure n
  | none => throw "Invalid decimal natural number"
def decodeBinder (j : Json) : Except String BinderInfo := do
  match ← j.getStr? with
  | "default" => pure .default
  | "implicit" => pure .implicit
  | "strictImplicit" => pure .strictImplicit
  | "instImplicit" => pure .instImplicit
  | other => throw s!"Unknown binder kind {other}"
def decodeDAG (dag : Json) : Except String Expr := do
  let mut names : Array Name := #[]
  for encoded in ← (← dag.getObjVal? "names").getArr? do
    let mut n := Name.anonymous
    for component in ← encoded.getArr? do
      let xs ← component.getArr?
      match ← xs[0]!.getStr? with
      | "str" => n := Name.str n (← xs[1]!.getStr?)
      | "num" => n := Name.num n (← decimal xs[1]!)
      | tag => throw s!"Unknown name component {tag}"
    names := names.push n
  let mut levels : Array Level := #[]
  for encoded in ← (← dag.getObjVal? "levels").getArr? do
    let xs ← encoded.getArr?
    let l ← match ← xs[0]!.getStr? with
      | "zero" => pure Level.zero
      | "succ" => pure (Level.succ (← tableValue levels xs[1]!))
      | "max" => pure (Level.max (← tableValue levels xs[1]!) (← tableValue levels xs[2]!))
      | "imax" => pure (Level.imax (← tableValue levels xs[1]!) (← tableValue levels xs[2]!))
      | "param" => pure (Level.param (← tableValue names xs[1]!))
      | tag => throw s!"Unknown universe constructor {tag}"
    levels := levels.push l
  let mut nodes : Array Expr := #[]
  for encoded in ← (← dag.getObjVal? "nodes").getArr? do
    let xs ← encoded.getArr?
    let e ← match ← xs[0]!.getStr? with
      | "bvar" => pure (Expr.bvar (← xs[1]!.getNat?))
      | "sort" => pure (Expr.sort (← tableValue levels xs[1]!))
      | "const" => pure (Expr.const (← tableValue names xs[1]!)
          ((← (← xs[2]!.getArr?).mapM (tableValue levels)).toList))
      | "app" => pure (Expr.app (← tableValue nodes xs[1]!) (← tableValue nodes xs[2]!))
      | "lam" => pure (Expr.lam (← tableValue names xs[1]!) (← tableValue nodes xs[2]!)
          (← tableValue nodes xs[3]!) (← decodeBinder xs[4]!))
      | "forall" => pure (Expr.forallE (← tableValue names xs[1]!) (← tableValue nodes xs[2]!)
          (← tableValue nodes xs[3]!) (← decodeBinder xs[4]!))
      | "let" => pure (Expr.letE (← tableValue names xs[1]!) (← tableValue nodes xs[2]!)
          (← tableValue nodes xs[3]!) (← tableValue nodes xs[4]!) (← xs[5]!.getBool?))
      | "lit_nat" => pure (Expr.lit (.natVal (← decimal xs[1]!)))
      | "lit_string" => pure (Expr.lit (.strVal (← xs[1]!.getStr?)))
      | "proj" => pure (Expr.proj (← tableValue names xs[1]!) (← xs[2]!.getNat?)
          (← tableValue nodes xs[3]!))
      | tag => throw s!"Unknown expression constructor {tag}"
    nodes := nodes.push e
  tableValue nodes (← dag.getObjVal? "root")
partial def eraseMetadata (e : Expr) : Expr :=
  e.replace fun
    | .mdata _ child => some (eraseMetadata child)
    | _ => none
def kernelType (e : Expr) : IO String := do
  let (root, s) ← (putExpr e).run {}
  let text := (Json.mkObj [("format",toJson "lean-kernel-expr-dag-v1"), ("root",toJson root),
    ("nodes",Json.arr s.nodes), ("levels",Json.arr s.levels), ("names",Json.arr s.names)]).compress
  let restored := Json.parse text >>= decodeDAG
  let .ok decoded := restored | throw (IO.userError s!"DAG decoding failed: {restored}")
  unless Expr.equal (eraseMetadata e) decoded do
    throw (IO.userError "Kernel type DAG failed structural round-trip comparison")
  return text
end DeclarationExport

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let mismatches := env.constants.fold (init := #[]) fun acc n _ =>
    let literal := n.toString.startsWith "Nonadditivity." || n.toString.startsWith "_private.Nonadditivity."
    if DeclarationExport.isProject n != literal then acc.push n else acc
  unless mismatches.isEmpty do throwError "Project selection differs from Audit: {mismatches}"
  let names := (env.constants.fold (init := #[]) fun acc n _ =>
    if DeclarationExport.isProject n then acc.push n else acc).qsort (fun a b => a.toString < b.toString)
  let recordsPath := (← IO.getEnv "NONADDITIVITY_DECLARATIONS_RECORDS").getD ".lake/declarations.records.jsonl"
  let progressPath := (← IO.getEnv "NONADDITIVITY_DECLARATIONS_PROGRESS").getD ".lake/export-declarations-progress.json"
  let mut previous : Array Json := #[]
  if ← System.FilePath.pathExists recordsPath then
    let source ← IO.FS.Handle.mk recordsPath .read
    while true do
      let line ← source.getLine
      if line.isEmpty then break
      unless line.trimAscii.toString.isEmpty do
        let .ok record := Json.parse line | throwError "Invalid checkpoint record"
        previous := previous.push record
  unless previous.size ≤ names.size do throwError "Too many checkpoint records"
  for i in [:previous.size] do
    let .ok saved := previous[i]!.getObjValAs? String "name" | throwError "Missing checkpoint name"
    unless saved == names[i]!.toString do throwError "Checkpoint inventory mismatch at {i}"
  let cachePath := (← IO.getEnv "NONADDITIVITY_DECLARATIONS_READABLE_CACHE").getD ".lake/declarations.readable-cache.jsonl"
  let mut readableCache : Std.HashMap String Json := {}
  if ← System.FilePath.pathExists cachePath then
    let source ← IO.FS.Handle.mk cachePath .read
    while true do
      let line ← source.getLine
      if line.isEmpty then break
      unless line.trimAscii.toString.isEmpty do
        let .ok record := Json.parse line | throwError "Invalid readable cache"
        let .ok name := record.getObjValAs? String "name" | throwError "Missing readable cache name"
        readableCache := readableCache.insert name record
  let checkpoint ← IO.FS.Handle.mk recordsPath .append
  let mark := fun (n : Name) (stage : String) (done : Nat) =>
    IO.FS.writeFile progressPath <| (Json.mkObj [("name",toJson n.toString),
      ("stage",toJson stage), ("completed",toJson done), ("total",toJson names.size)]).compress
  let records ← liftTermElabM do
    withOptions (fun o => o.setBool `pp.all false |>.setBool `pp.fullNames true |>.setBool `pp.universes true
      |>.setBool `pp.privateNames true |>.set `pp.maxSteps (10000000 : Nat)) do
      let mut records := previous
      for n in names.extract previous.size names.size do
        mark n "constant_info" records.size
        let info ← getConstInfo n
        let some moduleName ← findModuleOf? n | throwError "Missing source module for {n}"
        mark n "kernel_expr_dag" records.size
        let kernelText ← DeclarationExport.kernelType info.type
        let cached := readableCache[n.toString]?
        mark n "readable_type" records.size
        let readable ← match cached.bind (fun r => (r.getObjValAs? String "type_readable").toOption) with
          | some t => pure t | none => pure ((← PrettyPrinter.ppExpr info.type).pretty 100)
        mark n "type_references" records.size
        let typeRefs ← DeclarationExport.references info.type
        mark n "value_references" records.size
        let valueRefs ← match info.value? (allowOpaque := true) with
          | some v => DeclarationExport.references v | none => pure #[]
        let projectRefs := ((typeRefs ++ valueRefs).foldl (fun acc d =>
          if DeclarationExport.isProject d then acc.insert d else acc) ({} : NameHashSet)).toArray.qsort
            (fun a b => a.toString < b.toString)
        let record := Json.mkObj [("name",toJson n.toString), ("module",toJson moduleName.toString),
          ("file",toJson (moduleName.toString.replace "." "/" ++ ".lean")),
          ("kind",toJson (DeclarationExport.kind info)), ("level_parameters",toJson (info.levelParams.map Name.toString)),
          ("type",toJson kernelText), ("type_representation",toJson "lean-kernel-expr-dag-v1"),
          ("type_readable",toJson readable), ("is_internal",toJson n.isInternal),
          ("is_private",toJson (isPrivateName n)), ("is_internal_detail",toJson n.isInternalDetail),
          ("type_dependencies",toJson (typeRefs.map Name.toString)),
          ("value_dependencies",toJson (valueRefs.map Name.toString)),
          ("project_dependencies",toJson (projectRefs.map Name.toString)), ("source_range",Json.null)]
        checkpoint.putStrLn record.compress
        checkpoint.flush
        records := records.push record
        mark n "record_saved" records.size
      pure records
  let output := (← IO.getEnv "NONADDITIVITY_DECLARATIONS_RAW").getD ".lake/declarations.raw.json"
  IO.FS.writeFile output (Json.mkObj [("schema_version",toJson (1 : Nat)),
    ("count",toJson names.size), ("declarations",Json.arr records)]).compress
  logInfo s!"DECLARATION EXPORT PASSED: {names.size} project constants; {output}"
