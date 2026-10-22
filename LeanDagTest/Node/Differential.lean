import LeanDag.Node.Model.Run
import LeanDag.Node.Vote
import LeanDag.Scheme.Model.LeastSel
/-!
# The program against the scheme's decider, on random records

`docs/validator.md` §6, item 2. A seeded generator draws records of
eight rounds over four validators: at each round one validator may be
absent and validator `3` may equivocate, and each block references one
block of each of at least three authors of the round below, drawn at
random among twins. Each record goes into an empty store through the
program's store path (`flush`). On it, at five rows and schedules,
three computations give one decided prefix:

* the program's decision step at the bounded vote (`decideStep`), the
  store a map and the history computed by levels;
* the same at the least vote (`Scheme.leastSel`), which searches the
  voter's whole history;
* the scheme's *TryDecide* in its own order (`Scheme.schemeTryDecide`),
  rounds from the top down, at the least vote.

A fourth runs the program as it runs, a decision step after each round
arrives, restarting after the last decision output; it outputs the same.
-/

namespace LeanDagTest

namespace Node

namespace Differential

open LeanDag LeanDag.Node

/-- A step of a linear congruential generator. -/
def next (s : ℕ) : ℕ := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- A draw below `k`, and the next state. -/
def draw (s : ℕ) (k : ℕ) : ℕ × ℕ := let s' := next s; ((s' / 65536) % k, s')

/-- The blocks a record holds. -/
abbrev Blocks := List (ℕ × Block (Fin 4) ℕ Unit)

/-- One block per author among `as`, each drawn among that author's
blocks in `prev`. -/
def pick (prev : Blocks) : List (Fin 4) → ℕ → Finset ℕ × ℕ
  | [], s => (∅, s)
  | a :: as, s =>
    let mine := prev.filter fun e => e.2.creator = a
    let (i, s) := draw s mine.length
    let (rest, s) := pick prev as s
    match mine[i]? with
    | some e => (insert e.1 rest, s)
    | none => (rest, s)

/-- References into `prev`: every author of `prev`, less one drawn at
random when more than three remain. -/
def refsInto (prev : Blocks) (s : ℕ) : Finset ℕ × ℕ :=
  let as := (prev.map fun e => e.2.creator).dedup
  let (d, s) := draw s 10
  let (j, s) := draw s as.length
  let as := if 3 < as.length ∧ d < 4 then as.eraseIdx j else as
  pick prev as s

/-- The blocks of round `r` above `prev`, numbered from `id`: one
validator absent with probability `3/10`, and validator `3` with a twin
on other references with probability `3/10`. -/
def roundOf (prev : Blocks) (r id s : ℕ) : Blocks × ℕ :=
  let (d, s) := draw s 10
  let (gone, s) := draw s 4
  let authors := (List.finRange 4).filter fun v => ¬ (d < 3 ∧ v.val = gone)
  let (bs, id, s) := authors.foldl (fun (acc : Blocks × ℕ × ℕ) v =>
    let (bs, id, s) := acc
    let (refs, s) := refsInto prev s
    let b : Block (Fin 4) ℕ Unit := ⟨r, v, refs, ()⟩
    let (t, s) := draw s 10
    let (refs', s) := refsInto prev s
    if v.val = 3 ∧ t < 3 ∧ refs' ≠ refs then
      (bs ++ [(id, b), (id + 1, ⟨r, v, refs', ()⟩)], id + 2, s)
    else (bs ++ [(id, b)], id + 1, s)) ([], id, s)
  let _ := id
  (bs, s)

/-- A record of rounds `0 … R`, from seed `s`. -/
def record (R s : ℕ) : Blocks :=
  let gen : Blocks := (List.finRange 4).map fun v => (v.val, ⟨0, v, ∅, ()⟩)
  ((List.range R).foldl (fun (acc : Blocks × Blocks × ℕ) r =>
    let (all, prev, s) := acc
    let (bs, s) := roundOf prev (r + 1) (all.length) s
    (all ++ bs, bs, s)) (gen, gen, s)).1

/-- The record's hash: the identifier it gives a block. -/
def idIn (bs : Blocks) (b : Block (Fin 4) ℕ Unit) : ℕ :=
  ((bs.find? fun e => decide (e.2.round = b.round ∧ e.2.creator = b.creator ∧
    e.2.refs = b.refs)).map Prod.fst).getD 0

/-- A configuration at row `p`, `n = 4`, `f = 1`, `q = 3`, with `m`
leaders every `per` rounds, slot `k` led by `k % 4`, and the record's
hash. -/
def cfg (p : Scheme.Params) (per m : ℕ) (hper : 0 < per) (hm : 0 < m)
    (hb : ∀ k₁ k₂, k₁ / m = k₂ / m → (⟨k₁ % 4, by omega⟩ : Fin 4) = ⟨k₂ % 4, by omega⟩ → k₁ = k₂)
    (bs : Blocks) : Config (Fin 4) ℕ Unit where
  p := p
  f := 1
  c := 0
  q := 3
  me := 0
  per := per
  m := m
  per_pos := hper
  m_pos := hm
  elect := fun k => ⟨k % 4, by omega⟩
  elect_block := hb
  timeout := fun _ => 10
  σ := boundedSel
  idOf := idIn bs
  payload := fun _ => ()

/-- The record through the store path into an empty store. -/
def load (c : Config (Fin 4) ℕ Unit) (bs : Blocks) : State (Fin 4) ℕ Unit :=
  { State.init c with store := (flush c bs.length (Store.empty c.genesis) bs).1 }

/-- The decided prefix of one decision step. -/
def once (c : Config (Fin 4) ℕ Unit) (bs : Blocks) : List (ℕ × Option ℕ) :=
  commitsOf (decideStep c (load c bs)).2

/-- The scheme's *TryDecide* in its own order on the loaded store. -/
def scheme (c : Config (Fin 4) ℕ Unit) (bs : Blocks) : List (ℕ × Option ℕ) :=
  letI := c.slots
  let st := (load c bs).store
  Scheme.schemeTryDecide c.p Scheme.leastSel st.toRecord st.view c.per c.m 0 st.topRound

/-- The program as it runs: the rounds arrive one at a time, each
followed by a decision step. -/
def stepwise (c : Config (Fin 4) ℕ Unit) (bs : Blocks) (R : ℕ) : List (ℕ × Option ℕ) :=
  ((List.range (R + 1)).foldl (fun (acc : State (Fin 4) ℕ Unit × List (ℕ × Option ℕ)) r =>
    let (s, out) := acc
    let rb := bs.filter fun e => e.2.round = r
    let s := { s with store := (flush c rb.length s.store rb).1 }
    let d := decideStep c s
    (d.1, out ++ commitsOf d.2)) (State.init c, [])).2

/-- The five configurations: Mysticeti, Mahi-Mahi at wave four, Cordial
Miners and Bluestreak's partially synchronous row, one leader a round,
and Mysticeti with two leaders a round. -/
def cfgs (bs : Blocks) : List (Config (Fin 4) ℕ Unit) :=
  let one : ∀ k₁ k₂, k₁ / 1 = k₂ / 1 → (⟨k₁ % 4, by omega⟩ : Fin 4) = ⟨k₂ % 4, by omega⟩ →
      k₁ = k₂ := fun _ _ h _ => by simpa using h
  let two : ∀ k₁ k₂, k₁ / 2 = k₂ / 2 → (⟨k₁ % 4, by omega⟩ : Fin 4) = ⟨k₂ % 4, by omega⟩ →
      k₁ = k₂ := fun _ _ h h' => by simp only [Fin.mk.injEq] at h'; omega
  [cfg (Scheme.Params.mysticeti 4 1) 1 1 Nat.one_pos Nat.one_pos one bs,
   cfg (Scheme.Params.mahiMahi 4 4 1) 1 1 Nat.one_pos Nat.one_pos one bs,
   cfg (Scheme.Params.cordialMinersPS 4 1) 1 1 Nat.one_pos Nat.one_pos one bs,
   cfg (Scheme.Params.blueBottlePS 4 1) 1 1 Nat.one_pos Nat.one_pos one bs,
   cfg (Scheme.Params.mysticeti 4 1) 1 2 Nat.one_pos (by omega) two bs]

/-- Over seeds `0 … k − 1`: the runs, those where the four computations
agree and every block was accepted, and the commits and skips decided. -/
def summary (k : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (List.range k).foldl (fun acc seed =>
    let bs := record 8 seed
    (cfgs bs).foldl (fun (n, ok, cm, sk) c =>
      let d := once c bs
      let same := d = once { c with σ := Scheme.leastSel } bs ∧ d = scheme c bs ∧
        d = stepwise c bs 8 ∧ (load c bs).store.ids.card = bs.length
      (n + 1, if same then ok + 1 else ok, cm + (d.filter fun e => e.2.isSome).length,
        sk + (d.filter fun e => e.2.isNone).length)) acc) (0, 0, 0, 0)

/-- info: (200, 200, 1327, 143) -/
#guard_msgs in
#eval summary 40

end Differential

end Node

end LeanDagTest
