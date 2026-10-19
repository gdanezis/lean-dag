import LeanDagSim.Net
/-!
# `lake exe sim`

Runs one scenario and prints what each honest node reached and decided.
Options, each `--name value`: `row`, `n`, `f`, `c`, `seed`, `horizon`,
`gst`, `pre-max`, `delay-min`, `delay-max`, `timeout`, `lag`,
`crash` (`node@time,…`), `recover` (`node@down-up,…`), `byz` (`node,…`), `byz-until`, `withhold` (`z,v,R`: node `z` withholds
its round-`R` block from `v`) and `reveal-after`.
-/

open LeanDagSim

/-- Read `node@time,…`. -/
def parseCrash (s : String) : List (ℕ × ℕ) :=
  (s.splitOn ",").filterMap fun e =>
    match e.splitOn "@" with
    | [v, t] => do pure (← v.toNat?, ← t.toNat?)
    | _ => none

/-- Read `node@down-up,…`. -/
def parseRecover (s : String) : List (ℕ × ℕ × ℕ) :=
  (s.splitOn ",").filterMap fun e =>
    match e.splitOn "@" with
    | [v, w] => match w.splitOn "-" with
      | [d, u] => do pure (← v.toNat?, ← d.toNat?, ← u.toNat?)
      | _ => none
    | _ => none

/-- Read `node,…`. -/
def parseNats (s : String) : List ℕ := (s.splitOn ",").filterMap String.toNat?

/-- Apply the options to a scenario. -/
def parseArgs : List String → Scenario → Except String Scenario
  | [], sc => .ok sc
  | k :: v :: rest, sc => do
    let nat : Except String ℕ := match v.toNat? with
      | some x => .ok x
      | none => .error s!"{k}: not a number: {v}"
    let sc ← match k with
      | "--row" => pure { sc with row := v }
      | "--n" => pure { sc with n := ← nat }
      | "--f" => pure { sc with f := ← nat }
      | "--c" => pure { sc with c := ← nat }
      | "--seed" => pure { sc with seed := ← nat }
      | "--horizon" => pure { sc with horizon := ← nat }
      | "--gst" => pure { sc with gst := ← nat }
      | "--pre-max" => pure { sc with preMax := ← nat }
      | "--delay-min" => pure { sc with delayMin := ← nat }
      | "--delay-max" => pure { sc with delayMax := ← nat }
      | "--timeout" => pure { sc with timeout := ← nat }
      | "--lag" => pure { sc with lag := ← nat }
      | "--crash" => pure { sc with crash := parseCrash v }
      | "--recover" => pure { sc with recover := parseRecover v }
      | "--byz" => pure { sc with byz := parseNats v }
      | "--byz-until" => pure { sc with byzUntil := ← nat }
      | "--withhold" => match parseNats v with
        | [z, t, r] => pure { sc with withhold := some (z, t, r) }
        | _ => throw s!"--withhold wants z,v,R: {v}"
      | "--reveal-after" => pure { sc with revealAfter := ← nat }
      | _ => throw s!"unknown option {k}"
    parseArgs rest sc
  | [k], _ => .error s!"{k}: missing value"

def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .error e =>
    IO.eprintln e
    IO.eprintln s!"rows: {rows}"
    return 2
  | .ok sc =>
    let r := simulate sc
    if !r.admissible then
      IO.eprintln s!"row {sc.row} is not admissible at n={sc.n} f={sc.f} c={sc.c}"
      return 2
    IO.println s!"row {sc.row}  n={sc.n} f={sc.f} c={sc.c}  seed={sc.seed}  gst={sc.gst}"
    IO.println s!"time {r.time}  inputs {r.events}  largest store {r.maxStore} blocks"
    let honest := (List.range sc.n).filter fun v => !(sc.byz.contains v)
    for (v, top, ds) in (honest.zip (r.tops.zip r.commits)).map fun (v, t, d) => (v, t, d) do
      let skips := (ds.filter (·.2.isNone)).length
      IO.println s!"node {v}: round {top.getD 0}, {ds.length} slots decided, {skips} skipped"
    IO.println s!"agree {r.agree}  valid {r.valid}  jumps {r.jumps}"
    return if r.agree && r.valid then 0 else 1
