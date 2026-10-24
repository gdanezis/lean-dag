import LeanDagSim.Net
import Lean.Data.Json
import Mathlib.Data.Prod.Lex
/-!
# `lake exe node`

One honest node, speaking JSON lines. The first line configures it:
`{"row":"mysticeti","n":4,"f":1,"c":0,"me":0,"timeout":10}`.
Each further line is an input, and the node answers with one line per
output:

* inputs: `{"start":{}}`, `{"restart":{}}` (after a crash, from the
  persisted state), `{"timer":r}`, `{"deliver":{"peer":v,"block":block}}`
  (peer `v` announces its block), `{"stream":{"peer":v,"blocks":[…]}}` (a
  piece of peer `v`'s stream), and
  `{"syncRequest":{"peer":v,"target":t,"frontier":[…],"ids":[…]}}` (peer
  `v` asks for the history of `t` from its frontier, one round per
  validator, and for the blocks `ids` by name), and
  `{"ask":{"peer":v,"round":r}}` (peer `v` asks for the node's block of
  round `r`), with a block
  `{"id":i,"round":r,"creator":v,"refs":[…],"payload":p}` whose payload is
  `{"nonce":k,"ev":[[a,i,j],…],"ex":[a,…]}`: evidence that author `a`
  made the blocks `i` and `j` at one round, and the authors the block
  exposes;
* outputs: `{"persist":block}`, `{"broadcast":block}`,
  `{"setTimer":{"round":r,"after":t}}`, `{"commit":{"slot":k,"block":i}}`
  (`null` for a skip), `{"sync":{"peer":v,"target":t,"frontier":[…],"ids":[…]}}`
  (ask peer `v` for the history of `t`), `{"stream":{"peer":v,"blocks":[…]}}`
  (answer one), `{"ask":{"round":r}}` (ask every peer for its block of
  round `r`), and `{"send":{"peer":v,"block":block}}` (answer one).

A delivered block's identifier, if given, must be its hash
(`LeanDagSim.idOf`), and the node drops one that is not; if it is left
out, the node computes it.
-/

open Lean LeanDag LeanDag.Node LeanDagSim

/-- A field of a JSON object, as a natural number. -/
def natField (j : Json) (k : String) : Except String ℕ := do
  let v ← j.getObjVal? k
  v.getNat?

/-- A payload as JSON: its nonce, its evidence and the authors it exposes. -/
def payJson {n : ℕ} (p : Pay n) : Json :=
  Json.mkObj [("nonce", p.nonce),
    ("ev", Json.arr (((p.ev.image fun (e : Fin n × ℕ × ℕ) =>
        (toLex (e.1.val, toLex (e.2.1, e.2.2)) : Lex (ℕ × Lex (ℕ × ℕ)))).sort (· ≤ ·)).map
      fun e => Json.arr #[((ofLex e).1 : Json), ((ofLex (ofLex e).2).1 : Json),
        ((ofLex (ofLex e).2).2 : Json)]).toArray),
    ("ex", Json.arr ((p.ex.image Fin.val).sort (· ≤ ·) |>.map fun a => (a : Json)).toArray)]

/-- A block, with its identifier, as JSON. -/
def blockJson {n : ℕ} (id : ℕ) (b : Block (Fin n) ℕ (Pay n)) : Json :=
  Json.mkObj [("id", id), ("round", b.round), ("creator", b.creator.val),
    ("refs", Json.arr ((b.refs.sort (· ≤ ·)).map fun r => (r : Json)).toArray),
    ("payload", payJson b.payload)]

/-- An output, as JSON. -/
def outputJson {n : ℕ} : Output (Fin n) ℕ (Pay n) → Json
  | .persist id b => Json.mkObj [("persist", blockJson id b)]
  | .broadcast id b => Json.mkObj [("broadcast", blockJson id b)]
  | .setTimer r t => Json.mkObj [("setTimer", Json.mkObj [("round", r), ("after", t)])]
  | .commit k d => Json.mkObj [("commit", Json.mkObj [("slot", k),
      ("block", match d with | some i => (i : Json) | none => Json.null)])]
  | .sync peer t fr ids => Json.mkObj [("sync", Json.mkObj [("peer", peer.val), ("target", t),
      ("frontier", Json.arr ((List.finRange n).map fun v => (fr v : Json)).toArray),
      ("ids", Json.arr (ids.map fun i => (i : Json)).toArray)])]
  | .stream peer L => Json.mkObj [("stream", Json.mkObj [("peer", peer.val),
      ("blocks", Json.arr (L.map fun e => blockJson e.1 e.2).toArray)])]
  | .ask r => Json.mkObj [("ask", Json.mkObj [("round", r)])]
  | .send peer id b => Json.mkObj [("send", Json.mkObj [("peer", peer.val),
      ("block", blockJson id b)])]

/-- A block with its identifier, from JSON; the identifier is its hash
when left out. -/
def blockOf {n : ℕ} (d : Json) : Except String (ℕ × Block (Fin n) ℕ (Pay n)) := do
  let round ← natField d "round"
  let creator ← natField d "creator"
  let pj ← d.getObjVal? "payload"
  let nonce := (natField pj "nonce").toOption.getD (pj.getNat?.toOption.getD 0)
  let ev ← match pj.getObjVal? "ev" with
    | .ok a => a.getArr? >>= fun a => a.toList.mapM fun e => do
        let e ← e.getArr?
        let a ← (e[0]?.getD Json.null).getNat?
        let i ← (e[1]?.getD Json.null).getNat?
        let j ← (e[2]?.getD Json.null).getNat?
        if h : a < n then pure (⟨a, h⟩, i, j) else throw s!"author {a} out of range"
    | .error _ => pure []
  let ex ← match pj.getObjVal? "ex" with
    | .ok a => a.getArr? >>= fun a => a.toList.mapM fun x => do
        let x ← x.getNat?
        if h : x < n then pure (⟨x, h⟩ : Fin n) else throw s!"author {x} out of range"
    | .error _ => pure []
  let refs ← (← d.getObjVal? "refs").getArr?
  let refs ← refs.toList.mapM Json.getNat?
  if h : creator < n then
    let b : Block (Fin n) ℕ (Pay n) :=
      ⟨round, ⟨creator, h⟩, refs.toFinset, ⟨nonce, ev.toFinset, ex.toFinset⟩⟩
    return ((natField d "id").toOption.getD (idOf b), b)
  else throw s!"creator {creator} out of range"

/-- An input, from JSON. -/
def inputOf {n : ℕ} (hn : 0 < n) (j : Json) : Except String (Input (Fin n) ℕ (Pay n)) := do
  if (j.getObjVal? "start").isOk then return .start
  if (j.getObjVal? "restart").isOk then return .restart
  if let .ok r := natField j "timer" then return .timer r
  if let .ok f := j.getObjVal? "syncRequest" then
    let peer ← natField f "peer"
    let t ← natField f "target"
    let fr ← ((← f.getObjVal? "frontier").getArr?) >>= fun a => a.toList.mapM Json.getNat?
    let ids ← ((← f.getObjVal? "ids").getArr?) >>= fun a => a.toList.mapM Json.getNat?
    if h : peer < n then return .syncRequest ⟨peer, h⟩ t (fun v => fr.getD v.val 0) ids
    else throw s!"peer {peer} out of range"
  if let .ok f := j.getObjVal? "ask" then
    let peer ← natField f "peer"
    let r ← natField f "round"
    if h : peer < n then return .ask ⟨peer, h⟩ r
    else throw s!"peer {peer} out of range"
  if let .ok f := j.getObjVal? "stream" then
    let peer ← natField f "peer"
    let L ← ((← f.getObjVal? "blocks").getArr?) >>= fun a => a.toList.mapM blockOf
    if h : peer < n then return .stream ⟨peer, h⟩ L
    else throw s!"peer {peer} out of range"
  let d ← j.getObjVal? "deliver"
  let _ := hn
  let peer ← natField d "peer"
  let (id, b) ← blockOf (← d.getObjVal? "block")
  if h : peer < n then return .deliver ⟨peer, h⟩ id b
  else throw s!"peer {peer} out of range"

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
      timeout := get "timeout" 10 }
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
