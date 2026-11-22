import ContractMonitors

/-!
# `monitor`: run the synthesised monitors of the perception contracts

Reads one tick per line from standard input. A line lists the signals that
carry a value in the tick as `name=value`, separated by blanks; an empty line
is a tick without any signal. Writes one line per tick: the tick number and,
per monitor, `1` for an alarm and `0` otherwise.

    monitor [--list] [--params FILE]

`--list` prints name, component, and role of every monitor and exits.
`--params FILE` reads bounds as `key=value` lines.
-/

open ContractMonitors ContractMonitors.Perception

/-- A synthesised monitor together with its current state. -/
structure Running where
  M : Monitor Sig
  s : M.State

def Running.start (φ : Fml Sig) : Running :=
  ⟨synthMonitor φ, (synthMonitor φ).init⟩

def Running.step (r : Running) (x : Sig) : Running :=
  ⟨r.M, r.M.step r.s x⟩

def Running.alarm (r : Running) : Bool := !r.M.ok r.s

/-- Split `name=value`. -/
def parsePair (tok : String) : Option (String × Int) :=
  match tok.splitOn "=" with
  | [n, v] => v.toInt?.map fun i => (n, i)
  | _ => none

def parseTick (line : String) : Sig :=
  (line.splitOn " ").filterMap parsePair

def setParam (p : Params) (key : String) (v : Int) : Params :=
  match key with
  | "kIn" => { p with kIn := v.toNat }
  | "kDet" => { p with kDet := v.toNat }
  | "kTrk" => { p with kTrk := v.toNat }
  | "kPred" => { p with kPred := v.toNat }
  | "kConf" => { p with kConf := v.toNat }
  | "kFrozen" => { p with kFrozen := v.toNat }
  | "kProv" => { p with kProv := v.toNat }
  | "minPoints" => { p with minPoints := v }
  | "maxObjects" => { p with maxObjects := v }
  | "maxStep" => { p with maxStep := v }
  | "minConf" => { p with minConf := v }
  | "maxSpeed" => { p with maxSpeed := v }
  | _ => p

def readParams (path : String) : IO Params := do
  let text ← IO.FS.readFile path
  let pairs := (text.splitOn "\n").filterMap fun l => parsePair (l.replace " " "")
  return pairs.foldl (fun p (k, v) => setParam p k v) {}

partial def loop (stdin stdout : IO.FS.Stream) (rs : Array Running) (t : Nat) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then
    return
  let x := parseTick (line.replace "\n" "" |>.replace "\r" "")
  let rs := rs.map (·.step x)
  let cells := rs.toList.map fun r => if r.alarm then "1" else "0"
  stdout.putStrLn (",".intercalate (toString t :: cells))
  loop stdin stdout rs (t + 1)

def main (args : List String) : IO UInt32 := do
  let params ← match args.dropWhile (· != "--params") with
    | _ :: path :: _ => readParams path
    | _ => pure {}
  let ss := specs params
  let stdout ← IO.getStdout
  if args.contains "--list" then
    stdout.putStrLn "name,component,role"
    for s in ss do
      stdout.putStrLn s!"{s.name},{s.component},{s.role}"
    return 0
  stdout.putStrLn (",".intercalate ("tick" :: ss.map (·.name)))
  let stdin ← IO.getStdin
  loop stdin stdout (ss.map (fun s => Running.start s.fml)).toArray 1
  return 0
