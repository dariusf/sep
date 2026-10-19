import Bench.SmtLib.Parser

namespace Bench.SmtLib

def entlDirs : Array String :=
  #["onprob_qf_shid_entl", "qf_shid_entl", "qf_shidlia_entl", "qf_shlid_entl",
    "qf_shls_entl", "shid_entl", "shidlia_entl"]

def sweep (root : System.FilePath) : IO (Array (String × Option String)) := do
  let mut out := #[]
  for d in entlDirs do
    let dir := root / d
    if ← dir.isDir then
      let mut files := (← dir.readDir).map (·.path)
      files := files.filter fun p => p.extension == some "smt2"
      for p in files.qsort (fun a b => a.toString < b.toString) do
        match ← Parser.parseFile p with
        | .ok _ => out := out.push (p.toString, none)
        | .error e => out := out.push (p.toString, some e)
  return out

def sweepReport (root : System.FilePath) : IO Unit := do
  let rs ← sweep root
  let mut total := 0
  let mut bad := 0
  for d in entlDirs do
    let inDir := rs.filter fun (p, _) => (p.splitOn ("/" ++ d ++ "/")).length > 1
    let fails := inDir.filter fun (_, e) => e.isSome
    total := total + inDir.size
    bad := bad + fails.size
    IO.println s!"{d}: {inDir.size - fails.size}/{inDir.size} ok"
  IO.println s!"TOTAL: {total - bad}/{total} ok"
  for (p, e) in rs do
    match e with
    | some e => IO.println s!"FAIL {p}\n  {e}"
    | none => pure ()

end Bench.SmtLib
