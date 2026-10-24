import LeanDag.Scheme.Model.TryDecide
/-!
# An honest node — its interface

`docs/validator.md` §2. A node runs one row of the scheme as a pure
transition function from inputs to outputs. `Config` fixes the row, the
quorum, the node's identity, the schedule, the timeouts, the vote rule,
the identifier map and the payload source; `Input` and `Output` are the
events it consumes and produces.

A payload carries evidence of equivocation, an author with two of its
blocks, and the authors its block exposes (`Exposure`). The node checks the
row's validity `rowValid q E` on receipt: references one round below from
`q` distinct authors, and the exposure clause (`Clause.exposes`): the
block exposes the authors its evidence names and those its references
expose, and references none of them. It decides on a record of its memory
at `stored`, references one round below, and the honest set `∅`.

Definitions only.
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [DecidableEq Validator]

variable (Validator BlockId Payload) in
/-- **What a payload says of equivocation**: the evidence it carries, each
an author with two of its blocks, and the authors its block exposes. -/
structure Exposure where
  /-- The evidence a payload carries. -/
  ev : Payload → Finset (Validator × BlockId × BlockId)
  /-- The authors a payload's block exposes. -/
  ex : Payload → Finset Validator

/-- **The authors evidence names**: those it gives two distinct blocks of. -/
def named [DecidableEq BlockId] (E : Finset (Validator × BlockId × BlockId)) : Finset Validator :=
  (E.filter fun e => e.2.1 ≠ e.2.2).image (·.1)

/-- **The exposure clause**: a block exposes the authors its evidence names
and those its references expose, and references none of them. -/
def Clause.exposes [DecidableEq BlockId] (E : Exposure Validator BlockId Payload) :
    Clause Validator BlockId Payload := fun blk b =>
  E.ex b.payload = named (E.ev b.payload) ∪ b.refs.biUnion (fun j => E.ex (blk j).payload) ∧
    ∀ j ∈ b.refs, (blk j).creator ∉ E.ex b.payload

instance [DecidableEq BlockId] (E : Exposure Validator BlockId Payload)
    (blk : BlockId → Block Validator BlockId Payload) (b : Block Validator BlockId Payload) :
    Decidable (Clause.exposes E blk b) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **The node's validity**: references one round below from `q`
distinct authors, no author twice, and the exposure clause. Referencing
the author's own previous block is the honest build rule, not a validity
clause (`docs/validator.md` §8). -/
abbrev rowValid [DecidableEq BlockId] (q : ℕ) (E : Exposure Validator BlockId Payload) :
    Validity Validator BlockId Payload :=
  ValidAt q fun blk b => Clause.distinct blk b ∧ Clause.exposes E blk b

variable (Validator BlockId Payload) in
/-- **The validity a store's record carries**: references one round
below. -/
abbrev stored : Validity Validator BlockId Payload := ValidAt 0 Clause.none

variable (Validator BlockId Payload) [Fintype Validator] [LinearOrder BlockId]

/-- **A node's configuration.** The schedule is the scheme's,
`Slots.uniform per m elect`: `m` leaders every `per` rounds. -/
structure Config where
  /-- The row. -/
  p : Scheme.Params
  /-- The Byzantine bound. -/
  f : ℕ
  /-- The crash bound. -/
  c : ℕ
  /-- The quorum: authors a block references, and a round needs to advance. -/
  q : ℕ
  /-- The node itself. -/
  me : Validator
  /-- Rounds between slot rounds. -/
  per : ℕ
  /-- Leaders per slot round. -/
  m : ℕ
  per_pos : 0 < per
  m_pos : 0 < m
  /-- The leader of slot `k`. -/
  elect : ℕ → Validator
  /-- Distinct slots of one slot round have distinct leaders. -/
  elect_block : ∀ k₁ k₂, k₁ / m = k₂ / m → elect k₁ = elect k₂ → k₁ = k₂
  /-- The timeout of round `r`. -/
  timeout : ℕ → ℕ
  /-- The vote rule. -/
  σ : Scheme.VoteSel Validator BlockId Payload (stored Validator BlockId Payload) ∅
  /-- The identifier of a block: the environment's hash. -/
  idOf : Block Validator BlockId Payload → BlockId
  /-- What payloads say of equivocation. -/
  xp : Exposure Validator BlockId Payload
  /-- The payload of the node's round-`r` block, carrying the evidence `E`
  and exposing the authors `X`. -/
  payload : ℕ → Finset (Validator × BlockId × BlockId) → Finset Validator → Payload
  /-- The most blocks of a stream piece the node takes in at once. -/
  cap : ℕ

variable {Validator BlockId Payload}

namespace Config

variable (cfg : Config Validator BlockId Payload)

/-- The schedule. -/
abbrev slots : Slots Validator :=
  Slots.uniform cfg.per cfg.m cfg.per_pos cfg.m_pos cfg.elect cfg.elect_block

/-- The slots proposed at round `r`. -/
def slotsAt (r : ℕ) : List ℕ :=
  if r % cfg.per = 0 then (List.range cfg.m).map (fun i => cfg.m * (r / cfg.per) + i) else []

/-- **An admissible configuration**: the row is covered at the
committee's size, the bound `f` and the quorum `q`, its certificates fit
the quorum, and its commit threshold is reachable by the validators
neither Byzantine nor crash-prone, which is what liveness reads; a row
whose skip threshold is unreachable skips by the indirect rule. -/
def Admissible : Prop :=
  cfg.p.Covered (Fintype.card Validator) cfg.f cfg.q ∧ cfg.p.CertFits cfg.q ∧
    cfg.p.commitThreshold ≤ Fintype.card Validator - cfg.f - cfg.c ∧ 0 < cfg.q ∧
    cfg.q ≤ Fintype.card Validator

/-- **The payload source is faithful**: a payload reads back the evidence
and the exposed authors put in it. -/
def Faithful : Prop :=
  ∀ r E X, cfg.xp.ev (cfg.payload r E X) = E ∧ cfg.xp.ex (cfg.payload r E X) = X

instance : Decidable cfg.Admissible := by
  unfold Admissible Scheme.Params.Covered Scheme.Params.CertFits
    Scheme.Params.TwoRound Scheme.Params.ThreeRound Scheme.Params.TwoRoundCrash
    Scheme.Params.ThreeRoundCrash
  infer_instance

end Config

variable (Validator BlockId Payload)

/-- **What a node consumes.** -/
inductive Input where
  /-- Start: build the genesis block. -/
  | start
  /-- A block a peer sent in its own name, with its identifier: an
  announcement of its latest block. -/
  | deliver (peer : Validator) (id : BlockId) (b : Block Validator BlockId Payload)
  /-- A piece of a peer's stream. -/
  | stream (peer : Validator) (L : List (BlockId × Block Validator BlockId Payload))
  /-- The timer of round `r` fired. -/
  | timer (r : ℕ)
  /-- A peer asks for the history of the block `t` from its frontier `fr`,
  and for the blocks `ids` by name. -/
  | syncRequest (peer : Validator) (t : BlockId) (fr : Validator → ℕ) (ids : List BlockId)
  /-- A peer asks for the node's block of round `r`. -/
  | ask (peer : Validator) (r : ℕ)
  /-- The node restarts after a crash, from the state it persisted. -/
  | restart

/-- **What a node produces.** -/
inductive Output where
  /-- Write a block to storage; emitted before the block is broadcast. -/
  | persist (id : BlockId) (b : Block Validator BlockId Payload)
  /-- Send a block to every peer. -/
  | broadcast (id : BlockId) (b : Block Validator BlockId Payload)
  /-- Call back with `Input.timer r` after `after` ticks. -/
  | setTimer (r : ℕ) (after : ℕ)
  /-- Slot `k` is decided: committed to a block, or skipped. -/
  | commit (k : ℕ) (d : Option BlockId)
  /-- Ask the peer for the history of `t` from the frontier `fr`, and for
  the blocks `ids` by name. -/
  | sync (peer : Validator) (t : BlockId) (fr : Validator → ℕ) (ids : List BlockId)
  /-- Stream blocks to one peer, in order of round. -/
  | stream (peer : Validator) (L : List (BlockId × Block Validator BlockId Payload))
  /-- Ask every peer for its block of round `r`. -/
  | ask (r : ℕ)
  /-- Send one of the node's own blocks to one peer. -/
  | send (peer : Validator) (id : BlockId) (b : Block Validator BlockId Payload)

end Node

end LeanDag
