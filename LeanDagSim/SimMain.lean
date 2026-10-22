import LeanDagSim.Net
/-!
# `lake exe sim`

Runs one scenario and prints what each honest node reached and decided.
Options, each `--name value`: `row`, `n`, `f`, `c`, `seed`, `horizon`,
`gst`, `pre-max`, `delay-min`, `delay-max`, `timeout`, `lag`, `ahead`,
`crash` (`node@time,…`), `recover` (`node@down-up,…`), `byz` (`node,…`),
`byz-until`, `withhold` (`z,v,R`: node `z` withholds its round-`R` block
from `v`), `reveal-after`, `adv` (`node,…`: attackers), `slow` (`node,…`)
and `slow-delay` (the least delay to or from a slow node) and `slow-until`
(the tick it stops being slow), `leaders`
(`node,…`: the leader schedule, cycled), `attacks`
(`fake-base`, `split-base`, `fake-cert`, `conflict-proposals`,
`invalid-blocks`, `forged-author`, `flood`, `junk-at-cut`, `twin-split`, `hide`,
comma-separated), `limit`
(`ρ,W`: the rate limiter's quota and window) and `verify`
(`true` or `false`: whether the network checks signatures).
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
      | "--per" => pure { sc with per := ← nat }
      | "--ahead" => pure { sc with ahead := ← nat }
      | "--crash" => pure { sc with crash := parseCrash v }
      | "--recover" => pure { sc with recover := parseRecover v }
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
      | "--limit" => match parseNats v with
        | [ρ, W] => pure { sc with limit := some (ρ, W) }
        | _ => throw s!"--limit wants ρ,W: {v}"
      | "--attacks" => do
        let as ← (v.splitOn ",").mapM fun a => match a with
          | "fake-base" => pure Attack.fakeBase
          | "split-base" => pure Attack.splitBase
          | "fake-cert" => pure Attack.fakeCert
          | "hide" => pure Attack.hide
          | "conflict-proposals" => pure Attack.conflictProposals
          | "invalid-blocks" => pure Attack.invalidBlocks
          | "forged-author" => pure Attack.forgedAuthor
          | "flood" => pure Attack.flood
          | "junk-at-cut" => pure Attack.junkAtCut
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
    IO.println s!"time {r.time}  inputs {r.events}  largest store {r.maxStore} blocks  most pending {r.maxPending}"
    let honest := (List.range sc.n).filter sc.honest
    for (v, top, ds) in (honest.zip (r.tops.zip r.commits)).map fun (v, t, d) => (v, t, d) do
      let skips := (ds.filter (·.2.isNone)).length
      IO.println s!"node {v}: round {top.getD 0}, {ds.length} slots decided, {skips} skipped"
    IO.println (s!"junk chains {r.stats.junkChains}  asks {r.stats.asks}  " ++
      s!"adoptions {r.stats.adoptions}  stalls {r.stats.stalls} ({r.stats.stallsAfterGst} past GST)")
    for l in r.final do IO.println l
    IO.println s!"agree {r.agree}  prefixes {r.prefixes}  valid {r.valid}  skips {r.skips}  boots {r.boots}  dropped {r.dropped}"
    return if r.agree && r.valid then 0 else 1
