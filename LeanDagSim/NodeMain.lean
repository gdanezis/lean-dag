import LeanDagSim.Net
import Lean.Data.Json
/-!
# `lake exe node`

One honest node, speaking JSON lines. The first line configures it:
`{"row":"mysticeti","n":4,"f":1,"c":0,"me":0,"timeout":10,"lag":2}`.
Each further line is an input, and the node answers with one line per
output:

* inputs: `{"start":{}}`, `{"timer":r}`,
  `{"deliver":{"id":i,"round":r,"creator":v,"refs":[…],"payload":p}}`, and
  `{"fetchRequest":{"peer":v,"ids":[…]}}`;
* outputs: `{"persist":block}`, `{"broadcast":block}`,
  `{"setTimer":{"round":r,"after":t}}`, `{"commit":{"slot":k,"block":i}}`
  (`null` for a skip), `{"prune":G}`, `{"fetch":[…]}` (ask every peer),
  and `{"send":{"peer":v,"block":block}}` (answer one).

A delivered block's identifier, if given, must be its hash
(`LeanDagSim.idOf`), and the node drops one that is not; if it is left
out, the node computes it.
-/

open Lean LeanDag LeanDag.Node LeanDagSim

/-- A field of a JSON object, as a natural number. -/
def natField (j : Json) (k : String) : Except String ℕ := do
  let v ← j.getObjVal? k
  v.getNat?

/-- A block, with its identifier, as JSON. -/
def blockJson {n : ℕ} (id : ℕ) (b : Block (Fin n) ℕ ℕ) : Json :=
  Json.mkObj [("id", id), ("round", b.round), ("creator", b.creator.val),
    ("refs", Json.arr ((b.refs.sort (· ≤ ·)).map fun r => (r : Json)).toArray),
    ("payload", b.payload)]

/-- An output, as JSON. -/
def outputJson {n : ℕ} : Output (Fin n) ℕ ℕ → Json
  | .persist id b => Json.mkObj [("persist", blockJson id b)]
  | .broadcast id b => Json.mkObj [("broadcast", blockJson id b)]
  | .setTimer r t => Json.mkObj [("setTimer", Json.mkObj [("round", r), ("after", t)])]
  | .commit k d => Json.mkObj [("commit", Json.mkObj [("slot", k),
      ("block", match d with | some i => (i : Json) | none => Json.null)])]
  | .prune G => Json.mkObj [("prune", G)]
  | .fetch ids => Json.mkObj [("fetch", Json.arr (ids.map fun i => (i : Json)).toArray)]
  | .send peer id b => Json.mkObj [("send", Json.mkObj [("peer", peer.val),
      ("block", blockJson id b)])]
  | _ => Json.mkObj [("unsupported", Json.null)]

/-- An input, from JSON. -/
def inputOf {n : ℕ} (hn : 0 < n) (j : Json) : Except String (Input (Fin n) ℕ ℕ) := do
  if (j.getObjVal? "start").isOk then return .start
  if let .ok r := natField j "timer" then return .timer r
  if let .ok f := j.getObjVal? "fetchRequest" then
    let peer ← natField f "peer"
    let ids ← ((← f.getObjVal? "ids").getArr?) >>= fun a => a.toList.mapM Json.getNat?
    if h : peer < n then return .fetchRequest ⟨peer, h⟩ ids
    else throw s!"peer {peer} out of range"
  let d ← j.getObjVal? "deliver"
  let round ← natField d "round"
  let creator ← natField d "creator"
  let payload ← natField d "payload"
  let refs ← (← d.getObjVal? "refs").getArr?
  let refs ← refs.toList.mapM Json.getNat?
  if h : creator < n then
    let b : Block (Fin n) ℕ ℕ := ⟨round, ⟨creator, h⟩, refs.toFinset, payload⟩
    return .deliver ((natField d "id").toOption.getD (idOf b)) b
  else
    let _ := hn
    throw s!"creator {creator} out of range"

def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let line ← stdin.getLine
  let cfgJ ← match Json.parse line with
    | .ok j => pure j
    | .error e => do IO.eprintln s!"configuration: {e}"; return 2
  let get := fun (k : String) (d : ℕ) => (natField cfgJ k).toOption.getD d
  let row := (cfgJ.getObjValAs? String "row").toOption.getD "mysticeti"
  let sc : Scenario :=
    { row := row
      n := get "n" 4
      f := get "f" 1
      c := get "c" 0
      timeout := get "timeout" 10
      lag := get "lag" 2 }
  let me := get "me" 0
  match row? sc.row sc.n sc.f sc.c with
  | none => IO.eprintln s!"unknown row {row}"; return 2
  | some (p, q) =>
    if hn : 0 < sc.n then
      if hme : me < sc.n then
        let cfg := cfgFor sc p q hn ⟨me, hme⟩ 0
        if ¬ cfg.Admissible then
          IO.eprintln s!"row {row} is not admissible at n={sc.n} f={sc.f} c={sc.c}"
          return 2
        let mut s := State.init cfg
        repeat
          let line ← stdin.getLine
          if line.isEmpty then break
          if line.all Char.isWhitespace then continue
          match Json.parse line >>= inputOf hn with
          | .error e => IO.eprintln s!"input: {e}"
          | .ok i =>
            let r := step cfg s i
            s := r.1
            for o in r.2 do
              stdout.putStrLn (outputJson o).compress
            stdout.flush
        return 0
      else IO.eprintln s!"me {me} out of range"; return 2
    else IO.eprintln "n must be positive"; return 2
