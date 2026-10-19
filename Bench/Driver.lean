import Lean
import Bench.Slcomp

open Lean Elab Command

namespace Bench.Driver

def entlDirs : Array String :=
  #["onprob_qf_shid_entl", "qf_shid_entl", "qf_shidlia_entl", "qf_shlid_entl",
    "qf_shls_entl", "shid_entl", "shidlia_entl"]

def slcompBase : String := "https://github.com/sl-comp/bench/blob/main"

def yoloBase : String := "https://github.com/verse-lab/yolo/blob/main/SPLean/Experiments"

def yoloDir : String := "yolo"

structure Config where
  dirs : Array String := #[]
  filter : Option String := none
  timeoutMs : Nat := 10000
  csv : System.FilePath := "bench-results.csv"
  list : Bool := false
  deriving Inhabited

structure Problem where
  dir : String
  file : String
  path : System.FilePath
  source : String
  isLean : Bool
  deriving Inhabited

structure Result where
  dir : String
  file : String
  outcome : String
  ms : Nat
  reason : String
  source : String
  deriving Inhabited

def parseArgs (args : List String) : Except String Config :=
  go args {}
where
  go : List String → Config → Except String Config
    | [], c => .ok c
    | "--list" :: rest, c => go rest { c with list := true }
    | "--dir" :: d :: rest, c => go rest { c with dirs := c.dirs.push d }
    | "--filter" :: f :: rest, c => go rest { c with filter := some f }
    | "--timeout" :: t :: rest, c =>
      match t.toNat? with
      | some n => go rest { c with timeoutMs := n }
      | none => .error s!"--timeout expects a number, got {t}"
    | "--csv" :: p :: rest, c => go rest { c with csv := p }
    | a :: _, _ => .error s!"unknown argument: {a}"

def yoloSource (file : String) : String :=
  let base := file.dropEnd 5 |>.toString
  let up :=
    if base.startsWith "Cancel" then "cancel" ++ base.drop 6 else base
  s!"{yoloBase}/{up}.lean"

def collectFiles (root : System.FilePath) (ext : String) : IO (Array System.FilePath) := do
  if !(← root.pathExists) then
    return #[]
  let all ← root.walkDir
  let mut out := #[]
  for p in all do
    if p.extension == some ext && !(← p.isDir) then
      out := out.push p
  return out.qsort (fun a b => a.toString < b.toString)

def discover (cfg : Config) : IO (Array Problem) := do
  let wanted := cfg.dirs
  let mut probs := #[]
  for d in entlDirs do
    if wanted.isEmpty || wanted.contains d then
      for p in ← collectFiles ("sl-comp-bench" / d) "smt2" do
        let file := p.fileName.getD p.toString
        probs := probs.push
          { dir := d, file, path := p, source := s!"{slcompBase}/{d}/{file}", isLean := false }
  if wanted.isEmpty || wanted.contains yoloDir then
    let leanFiles ← collectFiles ("Bench" / "Yolo") "lean"
    for p in leanFiles.qsort (fun a b => a.toString < b.toString) do
      let file := p.fileName.getD p.toString
      probs := probs.push
        { dir := yoloDir, file, path := p, source := yoloSource file, isLean := true }
  match cfg.filter with
  | none => return probs
  | some f => return probs.filter fun p => f.isPrefixOf p.file || (p.file.splitOn f).length > 1

def runCommandElabM (env : Environment) (fileName : String) (tk : IO.CancelToken)
    (x : CommandElabM α) : IO (Except String α) := do
  let ctx : Command.Context :=
    { fileName, fileMap := default, snap? := none, cancelTk? := some tk }
  let st := Command.mkState env {} {}
  match ← (((x.run ctx).run' st).toBaseIO : BaseIO (Except Exception α)) with
  | .ok a => return .ok a
  | .error e => return .error (← e.toMessageData.toString)

def slcompProblem (path : System.FilePath) (timeoutMs : Nat) :
    CommandElabM (String × Nat × String) :=
  Bench.Slcomp.runProblem path timeoutMs

def runSmt2 (env : Environment) (p : Problem) (timeoutMs : Nat) (tk : IO.CancelToken) :
    IO (String × String) := do
  match ← runCommandElabM env p.path.toString tk (slcompProblem p.path timeoutMs) with
  | .ok (outcome, _, reason) => return (outcome, reason)
  | .error e => return ("failed", e)

abbrev EnvCache := IO.Ref (Array (Array Name × Environment))

def envForHeader (cache : EnvCache) (baseEnv : Environment) (inputCtx : Parser.InputContext)
    (header : Elab.HeaderSyntax) : IO Environment := do
  let imports := header.imports
  let names := imports.map (·.module)
  if names.all (fun n => n == `Init || baseEnv.allImportedModuleNames.contains n) then
    return baseEnv
  for (k, e) in ← cache.get do
    if k == names then
      return e
  let (env, _) ← Elab.processHeader header {} {} inputCtx
  cache.modify (·.push (names, env))
  return env

def runLeanFile (cache : EnvCache) (baseEnv : Environment) (p : Problem) :
    IO (String × String) := do
  let input ← IO.FS.readFile p.path
  let inputCtx := Parser.mkInputContext input p.path.toString
  let (header, parserState, msgs) ← Parser.parseHeader inputCtx
  let env ← envForHeader cache baseEnv inputCtx header
  let s ← Elab.IO.processCommands inputCtx parserState
    (Command.mkState env msgs {})
  let mut errs := #[]
  for m in s.commandState.messages.toList do
    if m.severity == .error then
      errs := errs.push (← m.data.toString)
  if errs.isEmpty then
    return ("proved", "")
  else
    return ("failed", errs[0]!)

partial def waitLoop (t : Task (Except IO.Error α)) (tk : IO.CancelToken) (timeoutMs : Nat)
    (start : Nat) : IO (Option (Except IO.Error α)) := do
  if ← IO.hasFinished t then
    return some t.get
  if (← IO.monoMsNow) - start > timeoutMs then
    tk.set
    IO.cancel t
    return none
  IO.sleep 5
  waitLoop t tk timeoutMs start

def runOne (cache : EnvCache) (baseEnv : Environment) (cfg : Config) (p : Problem) :
    IO Result := do
  let tk ← IO.CancelToken.new
  let start ← IO.monoMsNow
  let body : IO (String × String) :=
    if p.isLean then runLeanFile cache baseEnv p else runSmt2 baseEnv p cfg.timeoutMs tk
  let t ← IO.asTask body
  let r ← waitLoop t tk cfg.timeoutMs start
  let ms := (← IO.monoMsNow) - start
  match r with
  | none => return { dir := p.dir, file := p.file, outcome := "timeout", ms,
                     reason := s!"exceeded {cfg.timeoutMs} ms", source := p.source }
  | some (.error e) => return { dir := p.dir, file := p.file, outcome := "failed", ms,
                                reason := toString e, source := p.source }
  | some (.ok (outcome, reason)) =>
    return { dir := p.dir, file := p.file, outcome, ms, reason, source := p.source }

def csvField (s : String) : String :=
  let s := s.replace "\n" " " |>.replace "\r" " "
  if s.any (fun c => c == ',' || c == '"') then
    "\"" ++ s.replace "\"" "\"\"" ++ "\""
  else s

def writeCsv (path : System.FilePath) (rs : Array Result) : IO Unit := do
  let mut out := "dir,file,outcome,ms,reason,source\n"
  for r in rs do
    out := out ++ String.intercalate ","
      [csvField r.dir, csvField r.file, csvField r.outcome, toString r.ms,
       csvField r.reason, csvField r.source] ++ "\n"
  IO.FS.writeFile path out

def outcomes : Array String := #["proved", "failed", "unsupported", "parse-error", "timeout"]

def printSummary (rs : Array Result) : IO Unit := do
  let mut dirs := #[]
  for r in rs do
    if !dirs.contains r.dir then dirs := dirs.push r.dir
  for d in dirs do
    let sub := rs.filter (·.dir == d)
    let total := sub.foldl (fun a r => a + r.ms) 0
    let mean := if sub.isEmpty then 0 else total / sub.size
    let counts := outcomes.filterMap fun o =>
      let n := (sub.filter (·.outcome == o)).size
      if n == 0 then none else some s!"{o}={n}"
    IO.println s!"{d}: n={sub.size} {String.intercalate " " counts.toList} total={total}ms mean={mean}ms"
  IO.println s!"total: {rs.foldl (fun a r => a + r.ms) 0} ms"

def baseImports : Array Import :=
  #[{ module := `Sep.Xsearch }, { module := `Bench.Slcomp }]

def moduleAvailable (m : Name) : IO Bool := do
  try
    let p ← findOLean m
    p.pathExists
  catch _ =>
    return false

def loadBaseEnv : IO Environment := do
  unsafe Lean.enableInitializersExecution
  initSearchPath (← findSysroot)
  let mut avail := #[]
  for i in baseImports do
    if ← moduleAvailable i.module then
      avail := avail.push i
  if avail.isEmpty then
    avail := #[{ module := `Lean }]
  importModules avail {} (trustLevel := 1024) (loadExts := true)

def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error e => IO.eprintln e; return 1
  | .ok cfg =>
    let probs ← discover cfg
    if cfg.list then
      for p in probs do
        IO.println s!"{p.dir}\t{p.file}\t{p.source}"
      IO.println s!"{probs.size} problems"
      return 0
    let baseEnv ← loadBaseEnv
    let cache ← IO.mkRef #[]
    let mut rs := #[]
    for p in probs do
      let r ← runOne cache baseEnv cfg p
      IO.println s!"{r.dir}/{r.file}: {r.outcome} {r.ms}ms {r.reason}"
      rs := rs.push r
    writeCsv cfg.csv rs
    printSummary rs
    IO.println s!"csv: {cfg.csv}"
    return 0

end Bench.Driver
