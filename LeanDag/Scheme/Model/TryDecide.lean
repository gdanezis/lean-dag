import LeanDag.Scheme.Model.Rule
import Mathlib.Data.Finset.Max
/-!
# The commit loop

`docs/scheme.md` §8: the scheme's *TryDirectDecide*, *TryIndirectDecide*
and *TryDecide*, as functions of a validator's view. A decision is an
`Option (Option BlockId)`: `none` is undecided (the scheme's `⊥`),
`some none` a skip, `some (some L)` a commit of `L`. Slots are the
schedule's; the scheme scans rounds downward and, within a round, leader
indices downward, which is slot order reversed.

* `tryDirect`: skip if the blames reach the skip threshold, else commit
  the least candidate whose certificates reach the commit threshold. The
  tests are `schemeAnchored`'s `Skip`, `Commit` and `Link`, written out so
  that they are decidable.
* `tryIndirect`: walk the later slots in order, past the ineligible ones;
  stop undecided at the first undecided eligible slot, pass over skipped
  ones, and at the first committed one, the anchor, commit the least
  linked candidate or skip.
* `scan N m`: the decisions of the `m` slots `N + 1 − m, …, N`, oldest
  first, each slot decided from the decisions above it.
* `tryDecide lo N`: the longest prefix of decided slots from `lo`.
* `consumed`: the decisions output by successive calls on growing views,
  each restarting after the last decision output.
* `loopAssign`: the slot-to-block assignment the loop's decisions give,
  which the ledger (`commitSeq`, `ledgerSet`) reads.
* `schemeOrder`, `schemeTryDecide`: the scheme's loop in its own order,
  over rounds and leader indices, both downward.

Definitions only; the claims are `Scheme/Loop/Statement.lean`.
-/

namespace LeanDag

namespace Scheme

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable (p : Params) (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator]
variable (U : BlockRecord Validator BlockId Payload P honest) (V : U.View)

/-- The candidates of slot `k` the view holds (the scheme's `LeaderBlocks`). -/
def candidatesIn (k : ℕ) : Finset BlockId :=
  V.ids.filter (fun b => (U.block b).creator = S.leader k ∧ (U.block b).round = S.slotRound k)

/-- The least block of a set, if any. -/
def leastOf (s : Finset BlockId) : Option BlockId :=
  if h : s.Nonempty then some (s.min' h) else none

/-- **The scheme's *TryDirectDecide*.** -/
def tryDirect (k : ℕ) : Option (Option BlockId) :=
  if HoldsAtLeast U V p.skipThreshold (blamersAt p σ U k) then some none
  else (leastOf ((candidatesIn U V k).filter
    (fun L => (schemeAnchored p σ).Commit U V L (S.slotRound k) (S.kind k)))).map some

/-- **The scheme's *TryIndirectDecide***, over the decisions of the later slots, oldest
first. -/
def tryIndirect (k : ℕ) : List (ℕ × Option (Option BlockId)) → Option (Option BlockId)
  | [] => none
  | (j, s) :: rest =>
    if S.slotRound k + (p.waveLength - 1) + 1 ≤ S.slotRound j then
      match s with
      | none => none
      | some none => tryIndirect k rest
      | some (some A) =>
        some (leastOf ((candidatesIn U V k).filter
          (fun L => p.linkSize ≤ (creatorsOf U.block ((certsAt p σ U L (S.slotRound k)).filter
            (fun C => C ∈ history U A))).card)))
    else tryIndirect k rest

/-- One slot's decision: the direct rules, else the indirect rule. -/
def decideSlot (k : ℕ) (later : List (ℕ × Option (Option BlockId))) :
    Option (Option BlockId) :=
  match tryDirect p σ U V k with
  | some v => some v
  | none => tryIndirect p σ U V k later

/-- The decisions of the slots `N + 1 − m, …, N`, oldest first: the
scheme's list `S` after `m` steps of its downward scan. -/
def scan (N : ℕ) : ℕ → List (ℕ × Option (Option BlockId))
  | 0 => []
  | m + 1 => (N - m, decideSlot p σ U V (N - m) (scan N m)) :: scan N m

/-- The loop's decision for slot `k`, scanning to slot `N`. -/
def decisionAt (N k : ℕ) : Option (Option BlockId) :=
  decideSlot p σ U V k (scan p σ U V N (N - k))

/-- **The scheme's *TryDecide***: the longest prefix of decided slots from `lo` to `N`,
oldest first. -/
def tryDecide (lo N : ℕ) : List (ℕ × Option BlockId) :=
  ((scan p σ U V N (N + 1 - lo)).takeWhile (fun e => e.2.isSome)).map
    (fun e => (e.1, e.2.join))

/-- The loop's assignment, scanning to slot `N`: slot `k`'s committed block,
if any. -/
def loopAssign (N k : ℕ) : Option BlockId :=
  (decisionAt p σ U V N k).join

/-- The pairs of round and leader index the scheme's *TryDecide* visits, in
its order: the rounds from `rHigh` down to `rLast` that carry a wave
offset, every `per`-th round (`per = 1` with pipelining, the wave length
without), and at each the leader indices from `m − 1` down to `0`. -/
def schemeOrder (per m rLast rHigh : ℕ) : List (ℕ × ℕ) :=
  ((List.range' rLast (rHigh + 1 - rLast)).reverse.filter (fun r => r % per = 0)).flatMap
    (fun r => (List.range m).reverse.map (fun l => (r, l)))

/-- The slot of round `r` and leader index `l` in `Slots.uniform per m`. -/
def slotOf (per m r l : ℕ) : ℕ := r / per * m + l

/-- **The scheme's *TryDecide* in its own order**: visit `schemeOrder`,
decide each slot from the decisions already made and put it in front,
and return the longest decided prefix. -/
def schemeTryDecide (per m rLast rHigh : ℕ) : List (ℕ × Option BlockId) :=
  ((((schemeOrder per m rLast rHigh).foldl (fun Sd rl =>
      (slotOf per m rl.1 rl.2, decideSlot p σ U V (slotOf per m rl.1 rl.2) Sd) :: Sd) []).takeWhile
    (fun e => e.2.isSome)).map (fun e => (e.1, e.2.join)))

/-- The decisions the loop has output after `t` calls on the views `W 0, W 1, …`:
call `t` scans to slot `N t` on `W t` and restarts at the slot after the
last decision output so far, the scheme's `r_last`. -/
def consumed (lo : ℕ) (W : ℕ → U.View) (N : ℕ → ℕ) : ℕ → List (ℕ × Option BlockId)
  | 0 => []
  | t + 1 => consumed lo W N t ++
      tryDecide p σ U (W t) (lo + (consumed lo W N t).length) (N t)

end Scheme

end LeanDag
