import LeanDagSim.Net
/-!
# `lake exe sim`

Runs one scenario and prints what each honest node reached and decided.
Options, each `--name value`: `row`, `n`, `f`, `c`, `seed`, `horizon`,
`per`, `gst`, `pre-max`, `delay-min`, `delay-max`, `timeout`, `crash`
(`node@time,…`), `outage` (`node@from-until,…`: down from `from`,
restarting at `until`), `byz` (`node,…`), `byz-until`, `withhold` (`z,v,R`:
node `z` withholds its round-`R` block from `v`), `reveal-after`, `adv`
(`node,…`: attackers), `slow` (`node,…`), `slow-delay` (the least delay
to or from a slow node), `slow-until` (the tick it stops being slow),
`leaders` (`node,…`: the leader schedule, cycled), `attacks`
(`invalid-blocks`, `forged-author`, `twin-split`, comma-separated) and
`verify` (`true` or `false`: whether the network checks signatures).
-/

open LeanDagSim

/-- Read `node@time,…`. -/
def parseCrash (s : String) : List (ℕ × ℕ) :=
  (s.splitOn ",").filterMap fun e =>
    match e.splitOn "@" with
    | [v, t] => do pure (← v.toNat?, ← t.toNat?)
    | _ => none

/-- Read `node@from-until,…`. -/
def parseOutages (s : String) : List (ℕ × ℕ × ℕ) :=
  (s.splitOn ",").filterMap fun e =>
    match e.splitOn "@" with
    | [v, t] => match t.splitOn "-" with
      | [a, b] => do pure (← v.toNat?, ← a.toNat?, ← b.toNat?)
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
      | "--per" => pure { sc with per := ← nat }
      | "--crash" => pure { sc with crash := parseCrash v }
      | "--outage" => pure { sc with outages := parseOutages v }
      | "--byz" => pure { sc with byz := parseNats v }
      | "--byz-until" => pure { sc with byzUntil := ← nat }
      | "--withhold" => match parseNats v with
        | [z, t, r] => pure { sc with withhold := some (z, t, r) }
        | _ => throw s!"--withhold wants z,v,R: {v}"
      | "--reveal-after" => pure { sc with revealAfter := ← nat }
      | "--adv" => pure { sc with adv := parseNats v }
      | "--slow" => pure { sc with slow := parseNats v }
      | "--slow-delay" => pure { sc with slowDelay := ← nat }
      | "--slow-until" => pure { sc with slowUntil := some (← nat) }
      | "--leaders" => pure { sc with leaders := parseNats v }
      | "--attacks" => do
        let as ← (v.splitOn ",").mapM fun a => match a with
          | "invalid-blocks" => pure Attack.invalidBlocks
          | "forged-author" => pure Attack.forgedAuthor
          | "twin-split" => pure Attack.twinSplit
          | _ => throw s!"unknown attack {a}"
        pure { sc with attacks := as }
      | "--verify" => match v with
        | "true" => pure { sc with verify := true }
        | "false" => pure { sc with verify := false }
        | _ => throw s!"--verify wants true or false: {v}"
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
    IO.println (s!"time {r.time}  inputs {r.events}  largest disk {r.maxDisk} blocks  " ++
      s!"most syncs {r.maxSyncs}  most blocks a round {r.perRound.1} " ++
      s!"({r.perRound.2} not honest)")
    let honest := (List.range sc.n).filter sc.honest
    for (v, top, ds) in (honest.zip (r.tops.zip r.commits)).map fun (v, t, d) => (v, t, d) do
      let skips := (ds.filter (·.2.isNone)).length
      IO.println s!"node {v}: round {top.getD 0}, {ds.length} slots decided, {skips} skipped"
    IO.println (s!"requests {r.stats.requests} ({r.stats.named} asked by name)  " ++
      s!"pieces {r.stats.pieces} ({r.stats.streamed} blocks, {r.stats.served} served)  " ++
      s!"honest blocks not kept {r.stats.notKept}")
    for (v, _, b) in sc.outages do
      let (R, t₁, t₂) := recovery r v b
      let fmt (t : Option ℕ) := (t.map toString).getD "none"
      IO.println (s!"node {v} back at {b}: top round then {R}, node {v} above it at {fmt t₁}, " ++
        s!"first decision from then at {fmt t₂}")
    for l in r.final do IO.println l
    IO.println s!"agree {r.agree}  prefixes {r.prefixes}  valid {r.valid}  dropped {r.dropped}"
    return if r.agree && r.valid then 0 else 1
